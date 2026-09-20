import GerverSofa.KernelOnly.PartC.Stage4.PathDifferential
import GerverSofa.KernelOnly.PartC.Stage3.SupportDirect
import GerverSofa.KernelOnly.PartC.Stage2.NoHiddenCore

/-!
# Part C Stage 4: concrete geometry facts

C21: source-clean root closure.  In particular, branch decisions for the
literal nested-if path are made before endpoint abbreviations are unfolded.
The core-path nonnegativity statement is transported from the already sound
Part B cell enclosure instead of being reproved by a large transcendental
`nlinarith` call.
-/

noncomputable section

open Set

namespace GerverSofa
namespace PartC
namespace Stage4

open Stage2

private theorem T_nonneg : (0 : ℝ) ≤ T := by
  dsimp [T]
  positivity

private theorem T_le_pi : T ≤ Real.pi := by
  dsimp [T]
  nlinarith [Real.pi_pos]

private theorem rat_nonneg_cast {q : ℚ} (h : 0 ≤ q) : (0 : ℝ) ≤ (q : ℝ) := by
  exact_mod_cast h

private theorem rat_pos_cast {q : ℚ} (h : 0 < q) : (0 : ℝ) < (q : ℝ) := by
  exact_mod_cast h

theorem phi_pos : 0 < params.phi := Romik.phi_pos_of_mem_box params_mem

theorem phi_lt_theta : params.phi < params.theta := by
  have hphi := phi_bounds.2
  have htheta := theta_bounds.1
  norm_num at hphi htheta ⊢
  linarith

theorem theta_pos : 0 < params.theta := lt_trans phi_pos phi_lt_theta

theorem theta_lt_eta : params.theta < eta := by
  have htheta := theta_bounds.2
  norm_num at htheta
  dsimp [eta, T]
  nlinarith [Real.pi_gt_three]

theorem eta_lt_tau : eta < tau := by
  dsimp [eta, tau]
  linarith [phi_lt_theta]

theorem eta_lt_T : eta < T := by
  dsimp [eta]
  linarith [theta_pos]

theorem tau_lt_T : tau < T := by
  dsimp [tau]
  linarith [phi_pos]

theorem theta_lt_T : params.theta < T := lt_trans theta_lt_eta eta_lt_T

theorem phi_lt_T : params.phi < T := lt_trans phi_lt_theta theta_lt_T

theorem phi_lt_eta : params.phi < eta := lt_trans phi_lt_theta theta_lt_eta

theorem theta_lt_tau : params.theta < tau :=
  lt_trans theta_lt_eta eta_lt_tau

private theorem path_at_phi :
    Romik.path params params.phi = Romik.path1 params params.phi := by
  simp only [Romik.path, if_pos (le_refl params.phi)]

private theorem path_at_theta :
    Romik.path params params.theta = Romik.path2 params params.theta := by
  simp only [Romik.path, if_neg (not_le.mpr phi_lt_theta),
    if_pos (le_refl params.theta)]

private theorem path_at_eta :
    Romik.path params eta = Romik.path3 params eta := by
  have hraw : eta ≤ Real.pi / 2 - params.theta := by
    rfl
  simp only [Romik.path, if_neg (not_le.mpr phi_lt_eta),
    if_neg (not_le.mpr theta_lt_eta), if_pos hraw]

private theorem path_at_tau :
    Romik.path params tau = Romik.path4 params tau := by
  have hphi : ¬ tau ≤ params.phi := not_le.mpr (lt_trans phi_lt_theta theta_lt_tau)
  have htheta : ¬ tau ≤ params.theta := not_le.mpr theta_lt_tau
  have heta : ¬ tau ≤ Real.pi / 2 - params.theta := by
    simpa [eta, T] using (not_le.mpr eta_lt_tau)
  have htau : tau ≤ Real.pi / 2 - params.phi := by
    rfl
  simp only [Romik.path, if_neg hphi, if_neg htheta, if_neg heta, if_pos htau]

/-! ## C23: minimal exact reflection bridge

C22 tried to replace the whole scalar layer at once and regressed badly.  C23
rolls back to the stable C21 file and cherry-picks only the reflection bridge
needed for `D_theta_eq_path_tau`. -/

private def hReflect (z : Point) : Point :=
  (2 * params.k31 - z.1, z.2)

private theorem hReflect_involutive (z : Point) : hReflect (hReflect z) = z := by
  ext <;> simp [hReflect]

private theorem phase24_horizontal_reflection (t : ℝ) :
    (Romik.path4 params (T - t)).1 + (Romik.path2 params t).1 =
      params.k41 + params.k21 := by
  have hd1 := Romik.d1_eq_quarterPi_sub_b1_of_equations params_equations
  have hd2 := Romik.d2_eq_b2_add_quarterPi_correction_of_equations params_equations
  dsimp [T, Romik.path4, Romik.path2, Romik.rot, Romik.addK]
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub, hd1, hd2]
  ring

private theorem phase3_horizontal_reflection (t : ℝ) :
    (Romik.path3 params (T - t)).1 + (Romik.path3 params t).1 =
      2 * params.k31 := by
  have hc2 := Romik.c2_eq_c1_sub_halfPi_of_equations params_equations
  dsimp [T, Romik.path3, Romik.rot, Romik.addK]
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub, hc2]
  ring

private theorem k41_add_k21_eq_two_k31 :
    params.k41 + params.k21 = 2 * params.k31 := by
  have h24 := phase24_horizontal_reflection params.theta
  have h33 := phase3_horizontal_reflection params.theta
  have h23 := congrArg Prod.fst PartB.match23
  have h34 := congrArg Prod.fst PartB.match34
  simp only [eta, T] at h24 h33 h34
  linarith

private theorem phase24_reflect (t : ℝ) :
    Romik.path4 params (T - t) = hReflect (Romik.path2 params t) := by
  apply Prod.ext
  · have h := phase24_horizontal_reflection t
    rw [k41_add_k21_eq_two_k31] at h
    dsimp [hReflect]
    linarith
  · have h := Romik.phase24_vertical_reflection_of_equations params_equations t
    have hk := Romik.k42_eq_k22_of_equations params_equations
    rw [hk] at h
    have h' : (Romik.path4 params (T - t)).2 = (Romik.path2 params t).2 := by
      dsimp [T] at ⊢
      linarith [h]
    simpa [hReflect] using h'

private theorem phase3_reflect (t : ℝ) :
    Romik.path3 params (T - t) = hReflect (Romik.path3 params t) := by
  apply Prod.ext
  · have h := phase3_horizontal_reflection t
    dsimp [hReflect]
    linarith
  · have h := Romik.phase3_vertical_reflection_of_equations params_equations t
    simpa [T, hReflect] using h

private theorem rot_dot_u (t : ℝ) (z : Point) :
    dot (Romik.rot t z) (u t) = z.1 := by
  dsimp [dot, Romik.rot, u]
  calc
    (Real.cos t * z.1 - Real.sin t * z.2) * Real.cos t +
        (Real.sin t * z.1 + Real.cos t * z.2) * Real.sin t =
      z.1 * (Real.sin t ^ 2 + Real.cos t ^ 2) := by ring
    _ = z.1 := by rw [Real.sin_sq_add_cos_sq]; ring

private theorem rot_dot_v (t : ℝ) (z : Point) :
    dot (Romik.rot t z) (v t) = z.2 := by
  dsimp [dot, Romik.rot, v]
  calc
    (Real.cos t * z.1 - Real.sin t * z.2) * (-Real.sin t) +
        (Real.sin t * z.1 + Real.cos t * z.2) * Real.cos t =
      z.2 * (Real.sin t ^ 2 + Real.cos t ^ 2) := by ring
    _ = z.2 := by rw [Real.sin_sq_add_cos_sq]; ring

private theorem rot_injective (t : ℝ) : Function.Injective (Romik.rot t) := by
  intro x y h
  have hu := congrArg (fun z => dot z (u t)) h
  have hv := congrArg (fun z => dot z (v t)) h
  rw [rot_dot_u, rot_dot_u] at hu
  rw [rot_dot_v, rot_dot_v] at hv
  exact Prod.ext hu hv

private theorem matchPrime23 :
    Romik.pathPrime2 params params.theta =
      Romik.pathPrime3 params params.theta := by
  have h14 := congrFun params_equations (14 : Fin 22)
  have h15 := congrFun params_equations (15 : Fin 22)
  simp [Romik.Equations, Romik.system] at h14 h15
  apply Prod.ext <;> linarith

private theorem pathPrime2_eq_rot (p : Romik.Params) (t : ℝ) :
    Romik.pathPrime2 p t = Romik.rot t (Romik.alphaBeta2 p t) := rfl

private theorem pathPrime3_eq_rot (p : Romik.Params) (t : ℝ) :
    Romik.pathPrime3 p t = Romik.rot t (Romik.alphaBeta3 p t) := rfl

private theorem matchAB23 :
    Romik.alphaBeta2 params params.theta =
      Romik.alphaBeta3 params params.theta := by
  apply rot_injective params.theta
  simpa [pathPrime2_eq_rot, pathPrime3_eq_rot] using matchPrime23

private def reflAB (z : Point) : Point := (-z.2, -z.1)

private theorem ab3_reflect (t : ℝ) :
    Romik.alphaBeta3 params (T - t) = reflAB (Romik.alphaBeta3 params t) := by
  dsimp [T, reflAB, Romik.alphaBeta3]
  rw [Romik.c2_eq_c1_sub_halfPi_of_equations params_equations]
  ring

/-- Equation pair 20--21 is exactly the first niche contact. -/
theorem B_eta_eq_path_phi : B eta = Romik.path params params.phi := by
  have h20 := congrFun params_equations (20 : Fin 22)
  have h21 := congrFun params_equations (21 : Fin 22)
  simp [Romik.system] at h20 h21
  have h20' :
      (Romik.path1 params params.phi).1 -
          ((Romik.path3 params eta).1 -
            (Romik.alphaBeta3 params eta).1 * Real.sin eta) = 0 := by
    simpa [eta, T] using h20
  have h21' :
      (Romik.path1 params params.phi).2 -
          ((Romik.path3 params eta).2 +
            (Romik.alphaBeta3 params eta).1 * Real.cos eta) = 0 := by
    simpa [eta, T] using h21
  rw [path_at_phi]
  apply Prod.ext
  · change (Romik.path params eta).1 + alpha eta * (v eta).1 =
      (Romik.path1 params params.phi).1
    rw [path_at_eta]
    have ha : alpha eta = (Romik.alphaBeta3 params eta).1 := by
      simp only [alpha, alphaBetaAt, if_neg (not_le.mpr phi_lt_eta),
        if_neg (not_le.mpr theta_lt_eta), if_pos (le_refl eta)]
    rw [ha]
    simp only [v, Prod.fst]
    linarith
  · change (Romik.path params eta).2 + alpha eta * (v eta).2 =
      (Romik.path1 params params.phi).2
    rw [path_at_eta]
    have ha : alpha eta = (Romik.alphaBeta3 params eta).1 := by
      simp only [alpha, alphaBetaAt, if_neg (not_le.mpr phi_lt_eta),
        if_neg (not_le.mpr theta_lt_eta), if_pos (le_refl eta)]
    rw [ha]
    simp only [v, Prod.snd]
    linarith

/-- Reflected contact at the other end of the core. -/
theorem D_theta_eq_path_tau : D params.theta = Romik.path params tau := by
  have hb : beta params.theta = (Romik.alphaBeta2 params params.theta).2 := by
    simp only [beta, alphaBetaAt, if_neg (not_le.mpr phi_lt_theta),
      if_pos (le_refl params.theta)]
  have ha : alpha eta = (Romik.alphaBeta3 params eta).1 := by
    simp only [alpha, alphaBetaAt, if_neg (not_le.mpr phi_lt_eta),
      if_neg (not_le.mpr theta_lt_eta), if_pos (le_refl eta)]
  have h3 : Romik.path3 params eta = hReflect (Romik.path2 params params.theta) := by
    calc
      Romik.path3 params eta = hReflect (Romik.path3 params params.theta) := by
        simpa [eta] using phase3_reflect params.theta
      _ = hReflect (Romik.path2 params params.theta) := by
        exact congrArg hReflect PartB.match23.symm
  have hab0 : (Romik.alphaBeta3 params eta).1 =
      -(Romik.alphaBeta3 params params.theta).2 := by
    have h := congrArg Prod.fst (ab3_reflect params.theta)
    simpa [eta, reflAB] using h
  have hab : (Romik.alphaBeta3 params eta).1 =
      -(Romik.alphaBeta2 params params.theta).2 := by
    calc
      (Romik.alphaBeta3 params eta).1 =
          -(Romik.alphaBeta3 params params.theta).2 := hab0
      _ = -(Romik.alphaBeta2 params params.theta).2 := by
        rw [← congrArg Prod.snd matchAB23]
  have hDB : hReflect (D params.theta) = B eta := by
    rw [D, B, path_at_theta, path_at_eta, hb, ha, h3, hab]
    apply Prod.ext
    · simp [hReflect, u, v, eta, T, Real.sin_pi_div_two_sub,
        Real.cos_pi_div_two_sub]
      ring
    · simp [hReflect, u, v, eta, T, Real.sin_pi_div_two_sub,
        Real.cos_pi_div_two_sub]
      ring
  have hTau : Romik.path params tau = hReflect (Romik.path params params.phi) := by
    rw [path_at_tau, path_at_phi]
    calc
      Romik.path4 params tau = hReflect (Romik.path2 params params.phi) := by
        simpa [tau] using phase24_reflect params.phi
      _ = hReflect (Romik.path1 params params.phi) := by
        exact congrArg hReflect PartB.match12.symm
  have hDB' := congrArg hReflect hDB
  rw [hReflect_involutive] at hDB'
  calc
    D params.theta = hReflect (B eta) := hDB'
    _ = hReflect (Romik.path params params.phi) := congrArg hReflect B_eta_eq_path_phi
    _ = Romik.path params tau := hTau.symm

/-- The two base endpoints of the claimed niche boundary lie on `y=0`. -/
theorem B_T_y_zero : (B T).2 = 0 := by
  change (Romik.path params T).2 + alpha T * Real.cos T = 0
  have hEnd : (Romik.path params T).2 = 0 := by
    simpa [T] using pathEndYZero
  rw [hEnd]
  simp [T]

theorem D_zero_y_zero : (D 0).2 = 0 := by
  change (Romik.path params 0).2 - beta 0 * Real.sin 0 = 0
  rw [pathZero]
  norm_num

/-! Exact mesh transport for the literal core path.  Cells 1--62 are uniformly
above the base.  Cells 0 and 63 are intentionally excluded: their interval
hulls contain the terminal base contacts and have a tiny negative lower hull. -/
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
private theorem core_path_cell_lo_nonneg :
    ∀ i : PartB.Cell, 1 ≤ i.1 → i.1 ≤ 62 →
      (0 : ℚ) ≤ (PartB.cellPathInterval i).2.lo := by
  decide +kernel

/-! C30 strengthens the already kernel-checked cell statement from nonnegativity
to strict positivity on every core cell.  The computation is the same finite
exact-rational decision problem; only the target relation is stronger. -/
set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
private theorem core_path_cell_lo_pos :
    ∀ i : PartB.Cell, 1 ≤ i.1 → i.1 ≤ 62 →
      (0 : ℚ) < (PartB.cellPathInterval i).2.lo := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 100000000 in
private theorem cell1_path_y_lo_pos :
    (0 : ℚ) < (PartB.cellPathInterval (1 : PartB.Cell)).2.lo := by
  decide +kernel

/-- The first core contact is strictly above the base. -/
theorem B_eta_y_pos : 0 < (B eta).2 := by
  rw [B_eta_eq_path_phi]
  have hcell : params.phi ∈ PartB.cellSet (1 : PartB.Cell) :=
    ⟨Stage2.node1_lt_phi.le, Stage2.phi_lt_node2.le⟩
  have hphys : params.phi ∈ PartB.physicalInterval := by
    constructor
    · exact phi_pos.le
    · simpa [PartB.physicalInterval, T] using phi_lt_T.le
  have hcontains := PartB.cellPath_contains hcell hphys
  exact lt_of_lt_of_le (rat_pos_cast cell1_path_y_lo_pos) hcontains.2.1

/-- The reflected core contact has the same strictly positive height. -/
theorem D_theta_y_pos : 0 < (D params.theta).2 := by
  rw [D_theta_eq_path_tau, path_at_tau]
  have h24 := Romik.phase24_vertical_reflection_of_equations params_equations params.phi
  have h24' :
      (Romik.path4 params tau).2 - params.k42 =
        (Romik.path2 params params.phi).2 - params.k22 := by
    simpa [tau, T] using h24
  have hk := Romik.k42_eq_k22_of_equations params_equations
  have hm12y := congrArg Prod.snd PartB.match12
  have h := B_eta_y_pos
  rw [B_eta_eq_path_phi, path_at_phi] at h
  nlinarith

/-- Nonnegativity of the literal Gerver path on the core interval, transported
from the already proved Part B interval semantics. -/
theorem path_core_y_nonneg {t : ℝ} (ht : t ∈ Icc params.phi tau) :
    0 ≤ (Romik.path params t).2 := by
  have htPhys : t ∈ PartB.physicalInterval := by
    constructor
    · exact le_trans phi_pos.le ht.1
    · have htT : t ≤ T := le_trans ht.2 tau_lt_T.le
      simpa [PartB.physicalInterval, T] using htT
  rcases PartB.exists_cell_cover htPhys with ⟨i, hi⟩
  have hi1 : 1 ≤ i.1 := by
    by_contra hnot
    have hend : PartB.nodeTime (i.1 + 1) ≤ PartB.nodeTime 1 :=
      PartB.nodeTime_mono (by omega)
    linarith [Stage2.node1_lt_phi, hi.2, ht.1]
  have hi62 : i.1 ≤ 62 := by
    by_contra hnot
    have h63 : 63 ≤ i.1 := by omega
    have hstart : PartB.nodeTime 63 ≤ PartB.nodeTime i.1 :=
      PartB.nodeTime_mono h63
    linarith [Stage2.tau_lt_node63, hstart, hi.1, ht.2]
  have hcontains := PartB.cellPath_contains hi htPhys
  exact le_trans (rat_nonneg_cast (core_path_cell_lo_nonneg i hi1 hi62)) hcontains.2.1

/-- Strict positivity of the literal Gerver path height on the complete core
interval `[phi,tau]`.  C30 transports the exact strict lower hull proved above
through the existing Part B interval-containment theorem. -/
theorem path_core_y_pos {t : ℝ} (ht : t ∈ Icc params.phi tau) :
    0 < (Romik.path params t).2 := by
  have htPhys : t ∈ PartB.physicalInterval := by
    constructor
    · exact le_trans phi_pos.le ht.1
    · have htT : t ≤ T := le_trans ht.2 tau_lt_T.le
      simpa [PartB.physicalInterval, T] using htT
  rcases PartB.exists_cell_cover htPhys with ⟨i, hi⟩
  have hi1 : 1 ≤ i.1 := by
    by_contra hnot
    have hend : PartB.nodeTime (i.1 + 1) ≤ PartB.nodeTime 1 :=
      PartB.nodeTime_mono (by omega)
    linarith [Stage2.node1_lt_phi, hi.2, ht.1]
  have hi62 : i.1 ≤ 62 := by
    by_contra hnot
    have h63 : 63 ≤ i.1 := by omega
    have hstart : PartB.nodeTime 63 ≤ PartB.nodeTime i.1 :=
      PartB.nodeTime_mono h63
    linarith [Stage2.tau_lt_node63, hstart, hi.1, ht.2]
  have hcontains := PartB.cellPath_contains hi htPhys
  exact lt_of_lt_of_le (rat_pos_cast (core_path_cell_lo_pos i hi1 hi62)) hcontains.2.1

/-! A compact phase-2 lower bound for the reflected contact `D`.  It is also
used, by the exact phase-2/phase-4 reflection, to control the late `B` arc. -/
private theorem b1_lower_crude : (-53 / 100 : ℝ) ≤ params.b1 := by
  have hb := PartB.b1_contains.1
  norm_num [RatInterval.Contains, ExactReplay.fullInputBox, ExactReplay.getI,
    CertificateManifest.z22, CertificateManifest.q] at hb ⊢
  linarith

private theorem theta_upper_crude : params.theta ≤ (7 / 10 : ℝ) := by
  have h := theta_bounds.2
  norm_num at h ⊢
  linarith

private theorem k22_sub_b1_sub_one_nonneg :
    0 ≤ params.k22 - params.b1 - 1 := by
  have hk := PartB.k22_contains.1
  have hb := PartB.b1_contains.2
  norm_num [RatInterval.Contains, ExactReplay.fullInputBox, ExactReplay.getI,
    CertificateManifest.z22, CertificateManifest.q] at hk hb ⊢
  linarith

private theorem phase2_D_y_nonneg {t : ℝ}
    (ht0 : 0 ≤ t) (htθ : t ≤ params.theta) :
    0 ≤ (Romik.path2 params t).2 -
      (Romik.alphaBeta2 params t).2 * Real.sin t := by
  have hz : t / 2 - params.b1 - 1 ≤ 0 := by
    nlinarith [b1_lower_crude, theta_upper_crude]
  have hzc : t / 2 - params.b1 - 1 ≤
      (t / 2 - params.b1 - 1) * Real.cos t := by
    have hprod : 0 ≤
        (t / 2 - params.b1 - 1) * (Real.cos t - 1) :=
      mul_nonneg_of_nonpos_of_nonpos hz (sub_nonpos.mpr (Real.cos_le_one t))
    nlinarith
  have hs : Real.sin t ≤ t := Real.sin_le ht0
  simp [Romik.path2, Romik.rot, Romik.addK, Romik.alphaBeta2]
  nlinarith [hzc, hs, k22_sub_b1_sub_one_nonneg]

/-- Nonnegative height of the reflected early contact arc. -/
theorem D_y_nonneg {t : ℝ} (ht : t ∈ Icc (0 : ℝ) params.theta) : 0 ≤ (D t).2 := by
  by_cases hphi : t ≤ params.phi
  · have hpath : Romik.path params t = Romik.path1 params t := by
      simp only [Romik.path, if_pos hphi]
    have hb : beta t = (Romik.alphaBeta1 params t).2 := by
      simp only [beta, alphaBetaAt, if_pos hphi]
    change 0 ≤ (Romik.path params t).2 - beta t * Real.sin t
    rw [hpath, hb]
    have ha2 := Romik.a2_eq_neg_quarter_of_equations params_equations
    have hk12 := Romik.k12_eq_quarter_of_equations params_equations
    simp [Romik.path1, Romik.rot, Romik.addK, Romik.alphaBeta1, ha2, hk12]
    nlinarith [Real.sin_sq_add_cos_sq t, Real.cos_le_one t]
  · have hphi' : params.phi < t := lt_of_not_ge hphi
    have hpath : Romik.path params t = Romik.path2 params t := by
      simp only [Romik.path, if_neg hphi, if_pos ht.2]
    have hb : beta t = (Romik.alphaBeta2 params t).2 := by
      simp only [beta, alphaBetaAt, if_neg hphi, if_pos ht.2]
    change 0 ≤ (Romik.path params t).2 - beta t * Real.sin t
    rw [hpath, hb]
    exact phase2_D_y_nonneg ht.1 ht.2

/-- Nonnegative height of the reflected late contact arc. -/
theorem B_y_nonneg {t : ℝ} (ht : t ∈ Icc eta T) : 0 ≤ (B t).2 := by
  by_cases hetaEq : t = eta
  · subst t
    exact B_eta_y_pos.le
  have hetaT : eta < t := lt_of_le_of_ne ht.1 (Ne.symm hetaEq)
  by_cases htau : t ≤ tau
  · have hphiT : params.phi < t := lt_trans phi_lt_eta hetaT
    have hthetaT : params.theta < t := lt_trans theta_lt_eta hetaT
    have hpath : Romik.path params t = Romik.path4 params t := by
      have hetaRaw : ¬ t ≤ Real.pi / 2 - params.theta := by
        simpa [eta, T] using (not_le.mpr hetaT)
      have htauRaw : t ≤ Real.pi / 2 - params.phi := by
        simpa [tau, T] using htau
      simp only [Romik.path, if_neg (not_le.mpr hphiT),
        if_neg (not_le.mpr hthetaT), if_neg hetaRaw, if_pos htauRaw]
    have ha : alpha t = (Romik.alphaBeta4 params t).1 := by
      simp only [alpha, alphaBetaAt, if_neg (not_le.mpr hphiT),
        if_neg (not_le.mpr hthetaT), if_neg (not_le.mpr hetaT), if_pos htau]
    change 0 ≤ (Romik.path params t).2 + alpha t * Real.cos t
    rw [hpath, ha]
    let s : ℝ := T - t
    have hs0 : 0 ≤ s := by dsimp [s]; linarith [ht.2]
    have hsθ : s ≤ params.theta := by
      dsimp [s, eta] at *
      linarith
    have hD2 := phase2_D_y_nonneg hs0 hsθ
    have hd1 := Romik.d1_eq_quarterPi_sub_b1_of_equations params_equations
    have hk42 := Romik.k42_eq_k22_of_equations params_equations
    have hreflect :
        (Romik.path4 params t).2 +
            (Romik.alphaBeta4 params t).1 * Real.cos t =
          (Romik.path2 params s).2 -
            (Romik.alphaBeta2 params s).2 * Real.sin s := by
      dsimp [s, T]
      simp [Romik.path4, Romik.path2, Romik.rot, Romik.addK,
        Romik.alphaBeta4, Romik.alphaBeta2, hd1, hk42,
        Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
      ring
    rw [hreflect]
    exact hD2
  · have htauT : tau < t := lt_of_not_ge htau
    have hphiT : params.phi < t := lt_trans (lt_trans phi_lt_theta theta_lt_tau) htauT
    have hthetaT : params.theta < t := lt_trans theta_lt_tau htauT
    have hetaT' : eta < t := lt_trans eta_lt_tau htauT
    have hpath : Romik.path params t = Romik.path5 params t := by
      have hetaRaw : ¬ t ≤ Real.pi / 2 - params.theta := by
        simpa [eta, T] using (not_le.mpr hetaT')
      have htauRaw : ¬ t ≤ Real.pi / 2 - params.phi := by
        simpa [tau, T] using (not_le.mpr htauT)
      simp only [Romik.path, if_neg (not_le.mpr hphiT),
        if_neg (not_le.mpr hthetaT), if_neg hetaRaw, if_neg htauRaw]
    have ha : alpha t = (Romik.alphaBeta5 params t).1 := by
      simp only [alpha, alphaBetaAt, if_neg (not_le.mpr hphiT),
        if_neg (not_le.mpr hthetaT), if_neg (not_le.mpr hetaT'), if_neg htau]
    change 0 ≤ (Romik.path params t).2 + alpha t * Real.cos t
    rw [hpath, ha]
    have he2 := Romik.e2_eq_quarter_of_equations params_equations
    have hk52 := Romik.k52_eq_quarter_of_equations params_equations
    simp [Romik.path5, Romik.rot, Romik.addK, Romik.alphaBeta5, he2, hk52]
    nlinarith [Real.sin_sq_add_cos_sq t, Real.sin_le_one t]

/-! C31: strict positivity on the two open contact tails.  The base endpoints
`D 0` and `B T` have height exactly zero, so the natural domains are `Ioc`
and `Ico`.  These statements are used only for topology of the strict vertical
fills; the existing closed-interval nonnegativity theorems remain unchanged. -/
private theorem k22_sub_b1_sub_one_pos :
    0 < params.k22 - params.b1 - 1 := by
  have hk := PartB.k22_contains.1
  have hb := PartB.b1_contains.2
  norm_num [RatInterval.Contains, ExactReplay.fullInputBox, ExactReplay.getI,
    CertificateManifest.z22, CertificateManifest.q] at hk hb ⊢
  linarith

private theorem phase2_D_y_pos {t : ℝ}
    (ht0 : 0 ≤ t) (htθ : t ≤ params.theta) :
    0 < (Romik.path2 params t).2 -
      (Romik.alphaBeta2 params t).2 * Real.sin t := by
  have hz : t / 2 - params.b1 - 1 ≤ 0 := by
    nlinarith [b1_lower_crude, theta_upper_crude]
  have hzc : t / 2 - params.b1 - 1 ≤
      (t / 2 - params.b1 - 1) * Real.cos t := by
    have hprod : 0 ≤
        (t / 2 - params.b1 - 1) * (Real.cos t - 1) :=
      mul_nonneg_of_nonpos_of_nonpos hz (sub_nonpos.mpr (Real.cos_le_one t))
    nlinarith
  have hs : Real.sin t ≤ t := Real.sin_le ht0
  simp [Romik.path2, Romik.rot, Romik.addK, Romik.alphaBeta2]
  nlinarith [hzc, hs, k22_sub_b1_sub_one_pos]

/-- Strict height of the early reflected contact arc away from its base endpoint. -/
theorem D_y_pos {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) params.theta) :
    0 < (D t).2 := by
  by_cases hphi : t ≤ params.phi
  · have hpath : Romik.path params t = Romik.path1 params t := by
      simp only [Romik.path, if_pos hphi]
    have hb : beta t = (Romik.alphaBeta1 params t).2 := by
      simp only [beta, alphaBetaAt, if_pos hphi]
    change 0 < (Romik.path params t).2 - beta t * Real.sin t
    rw [hpath, hb]
    have ha2 := Romik.a2_eq_neg_quarter_of_equations params_equations
    have hk12 := Romik.k12_eq_quarter_of_equations params_equations
    have hcos : Real.cos t < 1 := by
      have hc := Real.cos_lt_cos_of_nonneg_of_le_pi
        (x := (0 : ℝ)) (y := t) (by norm_num)
        (le_trans ht.2 (le_trans theta_lt_T.le (by
          dsimp [T]
          linarith [Real.pi_pos]))) ht.1
      simpa using hc
    simp [Romik.path1, Romik.rot, Romik.addK, Romik.alphaBeta1, ha2, hk12]
    nlinarith [Real.sin_sq_add_cos_sq t, hcos]
  · have hpath : Romik.path params t = Romik.path2 params t := by
      simp only [Romik.path, if_neg hphi, if_pos ht.2]
    have hb : beta t = (Romik.alphaBeta2 params t).2 := by
      simp only [beta, alphaBetaAt, if_neg hphi, if_pos ht.2]
    change 0 < (Romik.path params t).2 - beta t * Real.sin t
    rw [hpath, hb]
    exact phase2_D_y_pos ht.1.le ht.2

/-- Strict height of the late contact arc away from its base endpoint. -/
theorem B_y_pos {t : ℝ} (ht : t ∈ Ico eta T) :
    0 < (B t).2 := by
  by_cases hetaEq : t = eta
  · subst t
    exact B_eta_y_pos
  have hetaT : eta < t := lt_of_le_of_ne ht.1 (Ne.symm hetaEq)
  by_cases htau : t ≤ tau
  · have hphiT : params.phi < t := lt_trans phi_lt_eta hetaT
    have hthetaT : params.theta < t := lt_trans theta_lt_eta hetaT
    have hpath : Romik.path params t = Romik.path4 params t := by
      have hetaRaw : ¬ t ≤ Real.pi / 2 - params.theta := by
        simpa [eta, T] using (not_le.mpr hetaT)
      have htauRaw : t ≤ Real.pi / 2 - params.phi := by
        simpa [tau, T] using htau
      simp only [Romik.path, if_neg (not_le.mpr hphiT),
        if_neg (not_le.mpr hthetaT), if_neg hetaRaw, if_pos htauRaw]
    have ha : alpha t = (Romik.alphaBeta4 params t).1 := by
      simp only [alpha, alphaBetaAt, if_neg (not_le.mpr hphiT),
        if_neg (not_le.mpr hthetaT), if_neg (not_le.mpr hetaT), if_pos htau]
    change 0 < (Romik.path params t).2 + alpha t * Real.cos t
    rw [hpath, ha]
    let s : ℝ := T - t
    have hs0 : 0 ≤ s := by
      dsimp [s]
      exact sub_nonneg.mpr ht.2.le
    have hsθ : s ≤ params.theta := by
      dsimp [s, eta] at *
      linarith
    have hD2 := phase2_D_y_pos hs0 hsθ
    have hd1 := Romik.d1_eq_quarterPi_sub_b1_of_equations params_equations
    have hk42 := Romik.k42_eq_k22_of_equations params_equations
    have hreflect :
        (Romik.path4 params t).2 +
            (Romik.alphaBeta4 params t).1 * Real.cos t =
          (Romik.path2 params s).2 -
            (Romik.alphaBeta2 params s).2 * Real.sin s := by
      dsimp [s, T]
      simp [Romik.path4, Romik.path2, Romik.rot, Romik.addK,
        Romik.alphaBeta4, Romik.alphaBeta2, hd1, hk42,
        Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
      ring
    rw [hreflect]
    exact hD2
  · have htauT : tau < t := lt_of_not_ge htau
    have hphiT : params.phi < t := lt_trans (lt_trans phi_lt_theta theta_lt_tau) htauT
    have hthetaT : params.theta < t := lt_trans theta_lt_tau htauT
    have hetaT' : eta < t := lt_trans eta_lt_tau htauT
    have hpath : Romik.path params t = Romik.path5 params t := by
      have hetaRaw : ¬ t ≤ Real.pi / 2 - params.theta := by
        simpa [eta, T] using (not_le.mpr hetaT')
      have htauRaw : ¬ t ≤ Real.pi / 2 - params.phi := by
        simpa [tau, T] using (not_le.mpr htauT)
      simp only [Romik.path, if_neg (not_le.mpr hphiT),
        if_neg (not_le.mpr hthetaT), if_neg hetaRaw, if_neg htauRaw]
    have ha : alpha t = (Romik.alphaBeta5 params t).1 := by
      simp only [alpha, alphaBetaAt, if_neg (not_le.mpr hphiT),
        if_neg (not_le.mpr hthetaT), if_neg (not_le.mpr hetaT'), if_neg htau]
    change 0 < (Romik.path params t).2 + alpha t * Real.cos t
    rw [hpath, ha]
    have he2 := Romik.e2_eq_quarter_of_equations params_equations
    have hk52 := Romik.k52_eq_quarter_of_equations params_equations
    have hsin : Real.sin t < 1 := by
      have hs := Real.sin_lt_sin_of_lt_of_le_pi_div_two
        (x := t) (y := T)
        (by
          have ht0 : 0 ≤ t :=
            le_trans theta_pos.le (le_trans theta_lt_eta.le ht.1)
          nlinarith [Real.pi_pos])
        (by simp [T]) ht.2
      simpa [T] using hs
    simp [Romik.path5, Romik.rot, Romik.addK, Romik.alphaBeta5, he2, hk52]
    nlinarith [Real.sin_sq_add_cos_sq t, hsin]

/-! ## C24: fixed-endpoint separation by a phase-2 Taylor bound and contact monotonicity

C23 reduced the root gate to four scalar `U(phi,t)` residuals.  This replacement
removes the large raw `nlinarith` calls.  Phase 2 is reduced to one variable
`d=t-phi` and certified by low-order alternating Taylor bounds.  Phases 3--5
use the exact contact identity `B(eta)=path(phi)` and the sign of the derivative
of the phase-local `B` contact projected on the fixed normal `u(t)`.
-/

private theorem phi_lower_crude : (39 / 1000 : ℝ) ≤ params.phi := by
  have h := phi_bounds.1
  norm_num at h ⊢
  linarith

private theorem phi_upper_crude : params.phi ≤ (1 / 20 : ℝ) := by
  have h := phi_bounds.2
  norm_num at h ⊢
  linarith

private theorem theta_upper_689 : params.theta ≤ (689 / 1000 : ℝ) := by
  have h := theta_bounds.2
  norm_num at h ⊢
  linarith

private theorem b1_upper_crude : params.b1 ≤ (-527 / 1000 : ℝ) := by
  have h := PartB.b1_contains.2
  norm_num [RatInterval.Contains, ExactReplay.fullInputBox, ExactReplay.getI,
    CertificateManifest.z22, CertificateManifest.q] at h ⊢
  linarith

private theorem b2_lower_crude : (9 / 10 : ℝ) ≤ params.b2 := by
  have h := PartB.b2_contains.1
  norm_num [RatInterval.Contains, ExactReplay.fullInputBox, ExactReplay.getI,
    CertificateManifest.z22, CertificateManifest.q] at h ⊢
  linarith

private theorem b2_upper_921 : params.b2 ≤ (921 / 1000 : ℝ) := by
  have h := PartB.b2_contains.2
  norm_num [RatInterval.Contains, ExactReplay.fullInputBox, ExactReplay.getI,
    CertificateManifest.z22, CertificateManifest.q] at h ⊢
  linarith

open scoped BigOperators
open Filter Finset

private theorem sin_taylor5_upper {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  have hanti : Antitone (ExactReplay.sinMagnitude x) :=
    ExactReplay.antitone_sinMagnitude hx0 hx1
  have htendRaw := (Real.hasSum_sin x).tendsto_sum_nat
  have htendMag :
      Filter.Tendsto
        (fun n : ℕ => ∑ i ∈ Finset.range n,
          (-1 : ℝ) ^ i * ExactReplay.sinMagnitude x i)
        Filter.atTop (nhds (Real.sin x)) := by
    simpa only [ExactReplay.sinMagnitude, mul_div_assoc] using htendRaw
  have hupper := Antitone.tendsto_le_alternating_series htendMag hanti 1
  have h3 : (2 * 1 + 1 : ℕ) = 3 := by norm_num
  rw [h3] at hupper
  have hsum :
      (∑ i ∈ Finset.range 3,
          (-1 : ℝ) ^ i * ExactReplay.sinMagnitude x i) =
        x - x ^ 3 / 6 + x ^ 5 / 120 := by
    norm_num [ExactReplay.sinMagnitude, Finset.sum_range_succ] <;> ring
  rw [hsum] at hupper
  exact hupper

private theorem cos_taylor6_lower {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 ≤ Real.cos x := by
  have hanti : Antitone (ExactReplay.cosMagnitude x) :=
    ExactReplay.antitone_cosMagnitude hx0 hx1
  have htendRaw := (Real.hasSum_cos x).tendsto_sum_nat
  have htendMag :
      Filter.Tendsto
        (fun n : ℕ => ∑ i ∈ Finset.range n,
          (-1 : ℝ) ^ i * ExactReplay.cosMagnitude x i)
        Filter.atTop (nhds (Real.cos x)) := by
    simpa only [ExactReplay.cosMagnitude, mul_div_assoc] using htendRaw
  have hlower := Antitone.alternating_series_le_tendsto htendMag hanti 2
  have h4 : (2 * 2 : ℕ) = 4 := by norm_num
  rw [h4] at hlower
  have hsum :
      (∑ i ∈ Finset.range 4,
          (-1 : ℝ) ^ i * ExactReplay.cosMagnitude x i) =
        1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 := by
    norm_num [ExactReplay.cosMagnitude, Finset.sum_range_succ] <;> ring
  rw [hsum] at hlower
  exact hlower

private theorem phase2_U_phi_formula {t : ℝ}
    (hphiT : params.phi < t) (htheta : t ≤ params.theta) :
    Stage2.UValue params.phi t =
      (-(1 / 4 : ℝ) * params.phi * params.phi +
          params.b1 * params.phi + params.b2) *
        (Real.cos (t - params.phi) - 1) +
      (params.phi / 2 - params.b1 - 1) * Real.sin (t - params.phi) +
      (params.phi / 2 - params.b1) * (t - params.phi) +
      (t - params.phi) * (t - params.phi) / 4 := by
  have hPhi2 : Romik.path params params.phi =
      Romik.path2 params params.phi := path_at_phi.trans PartB.match12
  have hPathT : Romik.path params t = Romik.path2 params t := by
    simp only [Romik.path, if_neg (not_le.mpr hphiT), if_pos htheta]
  unfold Stage2.UValue
  rw [hPhi2, hPathT]
  simp [dot, u, Romik.path2, Romik.rot, Romik.addK,
    Real.cos_sub, Real.sin_sub]
  ring_nf
  have hunit : Real.cos t ^ 2 + Real.sin t ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq t]
  have hb1collapse :
      params.b1 * Real.cos t ^ 2 * t + params.b1 * t * Real.sin t ^ 2 =
        params.b1 * t := by
    calc
      params.b1 * Real.cos t ^ 2 * t + params.b1 * t * Real.sin t ^ 2 =
          params.b1 * t * (Real.cos t ^ 2 + Real.sin t ^ 2) := by ring
      _ = params.b1 * t := by rw [hunit]; ring
  have hb2collapse :
      params.b2 * Real.cos t ^ 2 + params.b2 * Real.sin t ^ 2 =
        params.b2 := by
    calc
      params.b2 * Real.cos t ^ 2 + params.b2 * Real.sin t ^ 2 =
          params.b2 * (Real.cos t ^ 2 + Real.sin t ^ 2) := by ring
      _ = params.b2 := by rw [hunit]; ring
  have ht2collapse :
      Real.cos t ^ 2 * t ^ 2 * (1 / 4 : ℝ) +
          t ^ 2 * Real.sin t ^ 2 * (1 / 4 : ℝ) =
        t ^ 2 * (1 / 4 : ℝ) := by
    calc
      Real.cos t ^ 2 * t ^ 2 * (1 / 4 : ℝ) +
          t ^ 2 * Real.sin t ^ 2 * (1 / 4 : ℝ) =
          t ^ 2 * (1 / 4 : ℝ) * (Real.cos t ^ 2 + Real.sin t ^ 2) := by ring
      _ = t ^ 2 * (1 / 4 : ℝ) := by rw [hunit]; ring
  linarith [hb1collapse, hb2collapse, ht2collapse]

set_option maxHeartbeats 4000000 in
private theorem phase2_U_phi_nonneg {t : ℝ}
    (ht : t ∈ Icc params.phi params.theta) :
    0 ≤ Stage2.UValue params.phi t := by
  by_cases heq : t = params.phi
  · subst t
    simp [Stage2.UValue, dot]
  have hphiT : params.phi < t := lt_of_le_of_ne ht.1 (Ne.symm heq)
  let d : ℝ := t - params.phi
  let z1 : ℝ :=
    -(1 / 4 : ℝ) * params.phi * params.phi +
      params.b1 * params.phi + params.b2
  let z2 : ℝ := params.phi / 2 - params.b1 - 1
  let c : ℝ := params.phi / 2 - params.b1
  have hd0 : 0 ≤ d := by dsimp [d]; linarith
  have hdA : d ≤ (13 / 20 : ℝ) := by
    dsimp [d]
    linarith [theta_upper_689, phi_lower_crude, ht.2]
  have hd1 : d ≤ 1 := by linarith
  have hp0 : 0 ≤ params.phi := phi_pos.le
  have hb1lo := b1_lower_crude
  have hb1hi := b1_upper_crude
  have hz1nonneg : 0 ≤ z1 := by
    have hbp : 0 ≤ (params.b1 + 53 / 100) * params.phi :=
      mul_nonneg (by linarith) hp0
    have hpp : 0 ≤ params.phi * (1 / 20 - params.phi) :=
      mul_nonneg hp0 (by linarith [phi_upper_crude])
    dsimp [z1]
    nlinarith [b2_lower_crude, hbp, hpp]
  have hz1le : z1 ≤ (91 / 100 : ℝ) := by
    have hbp : params.b1 * params.phi ≤ (-527 / 1000 : ℝ) * (39 / 1000 : ℝ) := by
      have h1 := mul_le_mul_of_nonneg_right b1_upper_crude hp0
      have h2 := mul_le_mul_of_nonpos_left phi_lower_crude (by norm_num : (-527 / 1000 : ℝ) ≤ 0)
      exact le_trans h1 h2
    have hsquare : 0 ≤ params.phi * params.phi := mul_self_nonneg _
    dsimp [z1]
    nlinarith [b2_upper_921, hbp]
  have hz2lo : (-227 / 500 : ℝ) ≤ z2 := by
    dsimp [z2]
    linarith [phi_lower_crude, b1_upper_crude]
  have hz2hi : z2 ≤ 0 := by
    dsimp [z2]
    linarith [phi_upper_crude, hb1lo]
  have hclo : (273 / 500 : ℝ) ≤ c := by
    dsimp [c]
    linarith [phi_lower_crude, b1_upper_crude]
  have hsinU := sin_taylor5_upper hd0 hd1
  have hcosL := cos_taylor6_lower hd0 hd1
  let SU : ℝ := d - d ^ 3 / 6 + d ^ 5 / 120
  let CL : ℝ := -(d ^ 2) / 2 + d ^ 4 / 24 - d ^ 6 / 720
  have hd2le1 : d ^ 2 ≤ 1 := by
    have hprod : 0 ≤ d * (1 - d) := mul_nonneg hd0 (sub_nonneg.mpr hd1)
    nlinarith
  have hSU0 : 0 ≤ SU := by
    have hcube : d ^ 3 ≤ d := by
      have hprod : 0 ≤ d * (1 - d ^ 2) :=
        mul_nonneg hd0 (sub_nonneg.mpr hd2le1)
      nlinarith
    have hd5 : 0 ≤ d ^ 5 := by positivity
    dsimp [SU]
    nlinarith
  have hCL0 : CL ≤ 0 := by
    have hd2 : 0 ≤ d ^ 2 := sq_nonneg d
    have hd4le : d ^ 4 ≤ d ^ 2 := by
      have h := mul_nonneg hd2 (sub_nonneg.mpr hd2le1)
      nlinarith
    dsimp [CL]
    nlinarith [sq_nonneg (d ^ 3), hd4le]
  have hcosm1 : CL ≤ Real.cos d - 1 := by
    dsimp [CL] at *
    linarith
  have hsinSU : Real.sin d ≤ SU := by
    dsimp [SU]
    exact hsinU
  have hz1CL : (91 / 100 : ℝ) * CL ≤ z1 * CL := by
    exact mul_le_mul_of_nonpos_right hz1le hCL0
  have hz1cos : z1 * CL ≤ z1 * (Real.cos d - 1) := by
    exact mul_le_mul_of_nonneg_left hcosm1 hz1nonneg
  have hz2sin : z2 * SU ≤ z2 * Real.sin d := by
    exact mul_le_mul_of_nonpos_left hsinSU hz2hi
  have hz2SU : (-227 / 500 : ℝ) * SU ≤ z2 * SU := by
    exact mul_le_mul_of_nonneg_right hz2lo hSU0
  have hcD : (273 / 500 : ℝ) * d ≤ c * d := by
    exact mul_le_mul_of_nonneg_right hclo hd0
  let Q : ℝ :=
    (23 / 250 : ℝ) - (41 / 200) * d + (227 / 3000) * d ^ 2 +
      (91 / 2400) * d ^ 3 - (227 / 60000) * d ^ 4 -
      (91 / 72000) * d ^ 5
  let R : ℝ :=
    (14560000 * d ^ 4 + 53048000 * d ^ 3 - 402318800 * d ^ 2 -
      1133187220 * d + 1625028307 : ℝ) / 11520000000
  have hd2A : d ^ 2 ≤ (13 / 20 : ℝ) ^ 2 := by nlinarith
  have hR : 0 ≤ R := by
    dsimp [R]
    have h3 : 0 ≤ d ^ 3 := by positivity
    have h4 : 0 ≤ d ^ 4 := by positivity
    nlinarith
  have hQend : 0 < (71432009 / 230400000000 : ℝ) := by norm_num
  have hQfactor :
      Q - (71432009 / 230400000000 : ℝ) = ((13 / 20 : ℝ) - d) * R := by
    dsimp [Q, R]
    ring
  have hQ : 0 ≤ Q := by
    have hprod : 0 ≤ ((13 / 20 : ℝ) - d) * R :=
      mul_nonneg (sub_nonneg.mpr hdA) hR
    linarith
  have hL :
      0 ≤ (91 / 100 : ℝ) * CL + (-227 / 500 : ℝ) * SU +
        (273 / 500 : ℝ) * d + d * d / 4 := by
    have hid :
        (91 / 100 : ℝ) * CL + (-227 / 500 : ℝ) * SU +
            (273 / 500 : ℝ) * d + d * d / 4 = d * Q := by
      dsimp [CL, SU, Q]
      ring
    rw [hid]
    exact mul_nonneg hd0 hQ
  have hformula' :
      Stage2.UValue params.phi t =
        z1 * (Real.cos d - 1) + z2 * Real.sin d + c * d + d * d / 4 := by
    simpa [d, z1, z2, c] using phase2_U_phi_formula hphiT ht.2
  rw [hformula']
  nlinarith [hL, hz1CL, hz1cos, hz2sin, hz2SU, hcD]

private theorem pathPrime1_eq_rot (p : Romik.Params) (t : ℝ) :
    Romik.pathPrime1 p t = Romik.rot t (Romik.alphaBeta1 p t) := rfl

private theorem matchPrime12 :
    Romik.pathPrime1 params params.phi = Romik.pathPrime2 params params.phi := by
  have h10 := congrFun params_equations (10 : Fin 22)
  have h11 := congrFun params_equations (11 : Fin 22)
  simp [Romik.Equations, Romik.system] at h10 h11
  apply Prod.ext <;> linarith

private theorem matchAB12 :
    Romik.alphaBeta1 params params.phi = Romik.alphaBeta2 params params.phi := by
  apply rot_injective params.phi
  simpa [pathPrime1_eq_rot, pathPrime2_eq_rot] using matchPrime12

private theorem ab4_reflect_ab2 (t : ℝ) :
    Romik.alphaBeta4 params (T - t) = reflAB (Romik.alphaBeta2 params t) := by
  dsimp [T, reflAB, Romik.alphaBeta4, Romik.alphaBeta2]
  rw [Romik.d1_eq_quarterPi_sub_b1_of_equations params_equations,
      Romik.d2_eq_b2_add_quarterPi_correction_of_equations params_equations]
  ring

private theorem ab5_reflect_ab1 (t : ℝ) :
    Romik.alphaBeta5 params (T - t) = reflAB (Romik.alphaBeta1 params t) := by
  dsimp [T, reflAB, Romik.alphaBeta5, Romik.alphaBeta1]
  rw [Romik.e1_eq_a1_of_equations params_equations,
      Romik.e2_eq_neg_a2_of_equations params_equations]
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  ring

private theorem matchAB34 :
    Romik.alphaBeta3 params eta = Romik.alphaBeta4 params eta := by
  have h3 := ab3_reflect params.theta
  have h4 := ab4_reflect_ab2 params.theta
  have hm := congrArg reflAB matchAB23
  simpa [eta] using h3.trans (hm.symm.trans h4.symm)

private theorem matchAB45 :
    Romik.alphaBeta4 params tau = Romik.alphaBeta5 params tau := by
  have h4 := ab4_reflect_ab2 params.phi
  have h5 := ab5_reflect_ab1 params.phi
  have hm := congrArg reflAB matchAB12
  simpa [tau] using h4.trans (hm.symm.trans h5.symm)

private def phaseB3 (t : ℝ) : Point :=
  Romik.path3 params t + (Romik.alphaBeta3 params t).1 • v t
private def phaseB4 (t : ℝ) : Point :=
  Romik.path4 params t + (Romik.alphaBeta4 params t).1 • v t
private def phaseB5 (t : ℝ) : Point :=
  Romik.path5 params t + (Romik.alphaBeta5 params t).1 • v t

private theorem u_hasDerivAt_local (t : ℝ) : HasDerivAt u (v t) t := by
  change HasDerivAt (fun s : ℝ => (Real.cos s, Real.sin s))
    (-Real.sin t, Real.cos t) t
  exact (Real.hasDerivAt_cos t).prodMk (Real.hasDerivAt_sin t)

private theorem phaseB3_eq_A3_sub_u (t : ℝ) :
    phaseB3 t = Stage2.phaseA3 t - u t := by
  apply Prod.ext <;> simp [phaseB3, Stage2.phaseA3]

private theorem phaseB4_eq_A4_sub_u (t : ℝ) :
    phaseB4 t = Stage2.phaseA4 t - u t := by
  apply Prod.ext <;> simp [phaseB4, Stage2.phaseA4]

private theorem phaseB5_eq_A5_sub_u (t : ℝ) :
    phaseB5 t = Stage2.phaseA5 t - u t := by
  apply Prod.ext <;> simp [phaseB5, Stage2.phaseA5]

private theorem B_eq_phaseB3 {t : ℝ} (ht : t ∈ Icc params.theta eta) :
    B t = phaseB3 t := by
  by_cases h : t = params.theta
  · subst t
    rw [B, path_at_theta]
    have ha : alpha params.theta = (Romik.alphaBeta2 params params.theta).1 := by
      simp only [alpha, alphaBetaAt, if_neg (not_le.mpr phi_lt_theta),
        if_pos (le_refl params.theta)]
    rw [ha]
    have hm := PartB.match23
    rw [hm, matchAB23]
    apply Prod.ext <;> simp [phaseB3, v]
  · have htheta : params.theta < t := lt_of_le_of_ne ht.1 (Ne.symm h)
    have hphi : params.phi < t := lt_trans phi_lt_theta htheta
    have hetaRaw : t ≤ Real.pi / 2 - params.theta := by
      simpa [eta, T] using ht.2
    apply Prod.ext <;> simp [B, alpha, alphaBetaAt, Romik.path, phaseB3,
      not_le.mpr hphi, not_le.mpr htheta, hetaRaw, ht.2, eta, T]

private theorem B_eq_phaseB4 {t : ℝ} (ht : t ∈ Icc eta tau) :
    B t = phaseB4 t := by
  by_cases h : t = eta
  · subst t
    have hB3 := B_eq_phaseB3 (t := eta) ⟨theta_lt_eta.le, le_rfl⟩
    have hm : Romik.path3 params eta = Romik.path4 params eta := by
      simpa [eta, T] using PartB.match34
    calc
      B eta = phaseB3 eta := hB3
      _ = phaseB4 eta := by
        unfold phaseB3 phaseB4
        rw [hm, matchAB34]
  · have hetaT : eta < t := lt_of_le_of_ne ht.1 (Ne.symm h)
    have htheta : params.theta < t := lt_trans theta_lt_eta hetaT
    have hphi : params.phi < t := lt_trans phi_lt_theta htheta
    have hetaRaw : Real.pi / 2 - params.theta < t := by
      simpa [eta, T] using hetaT
    have htauRaw : t ≤ Real.pi / 2 - params.phi := by
      simpa [tau, T] using ht.2
    apply Prod.ext <;> simp [B, alpha, alphaBetaAt, Romik.path, phaseB4,
      not_le.mpr hphi, not_le.mpr htheta, not_le.mpr hetaRaw, htauRaw,
      not_le.mpr hetaT, ht.2, eta, tau, T]

private theorem B_eq_phaseB5 {t : ℝ} (ht : t ∈ Icc tau T) :
    B t = phaseB5 t := by
  by_cases h : t = tau
  · subst t
    have hB4 := B_eq_phaseB4 (t := tau) ⟨eta_lt_tau.le, le_rfl⟩
    have hm : Romik.path4 params tau = Romik.path5 params tau := by
      simpa [tau, T] using PartB.match45
    calc
      B tau = phaseB4 tau := hB4
      _ = phaseB5 tau := by
        unfold phaseB4 phaseB5
        rw [hm, matchAB45]
  · have htauT : tau < t := lt_of_le_of_ne ht.1 (Ne.symm h)
    have hetaT : eta < t := lt_trans eta_lt_tau htauT
    have htheta : params.theta < t := lt_trans theta_lt_eta hetaT
    have hphi : params.phi < t := lt_trans phi_lt_theta htheta
    have hetaRaw : Real.pi / 2 - params.theta < t := by
      simpa [eta, T] using hetaT
    have htauRaw : Real.pi / 2 - params.phi < t := by
      simpa [tau, T] using htauT
    apply Prod.ext <;> simp [B, alpha, alphaBetaAt, Romik.path, phaseB5,
      not_le.mpr hphi, not_le.mpr htheta, not_le.mpr hetaRaw,
      not_le.mpr htauRaw, not_le.mpr hetaT, not_le.mpr htauT, eta, tau, T]

private theorem c1_le_theta : params.c1 ≤ params.theta := by
  have hc := PartB.c1_contains.2
  have ht := theta_bounds.1
  norm_num [RatInterval.Contains, ExactReplay.fullInputBox, ExactReplay.getI,
    CertificateManifest.z22, CertificateManifest.q] at hc ht ⊢
  linarith

private theorem eta_lower_four_fifths : (4 / 5 : ℝ) ≤ eta := by
  dsimp [eta, T]
  nlinarith [Real.pi_gt_three, theta_upper_crude]

private theorem d1_upper_33_25 : params.d1 ≤ (33 / 25 : ℝ) := by
  have hd := PartB.d1_contains.2
  norm_num [RatInterval.Contains, ExactReplay.fullInputBox, ExactReplay.getI,
    CertificateManifest.z22, CertificateManifest.q] at hd ⊢
  linarith

private theorem phaseB3_coeff_nonpos {q : ℝ} (hq : params.theta ≤ q) :
    params.c1 - q ≤ 0 := by linarith [c1_le_theta]

private theorem phaseB4_coeff_nonpos {q : ℝ} (hq : eta ≤ q) :
    params.d1 - q / 2 - 1 ≤ 0 := by
  nlinarith [d1_upper_33_25, eta_lower_four_fifths]

private theorem dot_hasDerivAt_fixed_local {f : ℝ → Point} {df : Point} {t : ℝ}
    (h : HasDerivAt f df t) (w : Point) :
    HasDerivAt (fun s => dot (f s) w) (dot df w) t := by
  have h1 := HasDerivAt.const_mul w.1 h.fst
  have h2 := HasDerivAt.const_mul w.2 h.snd
  have hs := h1.fun_add h2
  simpa [dot, mul_comm] using hs

private theorem phaseB3_dot_hasDerivAt (s t : ℝ) :
    HasDerivAt (fun q => dot (phaseB3 q) (u s))
      (dot ((params.c1 - t) • v t) (u s)) t := by
  have h := (Stage2.A3_hasDerivAt_public t).fun_sub (u_hasDerivAt_local t)
  have hd : ((1 + params.c1 - t) • v t) - v t =
      (params.c1 - t) • v t := by
    apply Prod.ext <;> simp [v] <;> ring
  rw [hd] at h
  have hdot := dot_hasDerivAt_fixed_local h (u s)
  simpa only [phaseB3_eq_A3_sub_u] using hdot

private theorem phaseB4_dot_hasDerivAt (s t : ℝ) :
    HasDerivAt (fun q => dot (phaseB4 q) (u s))
      (dot ((params.d1 - t / 2 - 1) • v t) (u s)) t := by
  have h := (Stage2.A4_hasDerivAt_public t).fun_sub (u_hasDerivAt_local t)
  have hd : ((params.d1 - t / 2) • v t) - v t =
      (params.d1 - t / 2 - 1) • v t := by
    apply Prod.ext <;> simp [v] <;> ring
  rw [hd] at h
  have hdot := dot_hasDerivAt_fixed_local h (u s)
  simpa only [phaseB4_eq_A4_sub_u] using hdot

private theorem phaseB5_dot_hasDerivAt (s t : ℝ) :
    HasDerivAt (fun q => dot (phaseB5 q) (u s))
      (dot ((-(1 / 2 : ℝ)) • v t) (u s)) t := by
  have h := (Stage2.A5_hasDerivAt_public t).fun_sub (u_hasDerivAt_local t)
  have hd : ((1 / 2 : ℝ) • v t) - v t = (-(1 / 2 : ℝ)) • v t := by
    apply Prod.ext <;> simp [v] <;> ring
  rw [hd] at h
  have hdot := dot_hasDerivAt_fixed_local h (u s)
  simpa only [phaseB5_eq_A5_sub_u] using hdot

private theorem phaseB_mono_left
    {F : ℝ → Point} {r : ℝ → ℝ} {a b s : ℝ}
    (hder : ∀ q,
      HasDerivAt (fun x => dot (F x) (u s))
        (dot ((r q) • v q) (u s)) q)
    (hr : ∀ q ∈ Ioo a b, r q ≤ 0)
    (hs0 : 0 ≤ s) (hsa : s ≤ a) (hbT : b ≤ T) :
    MonotoneOn (fun q => dot (F q) (u s)) (Icc a b) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg
    (f' := fun q => dot ((r q) • v q) (u s)) (convex_Icc a b) ?_ ?_ ?_
  · intro q hq
    exact (hder q).continuousAt.continuousWithinAt
  · intro q hq
    exact (hder q).hasDerivWithinAt
  · intro q hq
    have hi : q ∈ Ioo a b := by simpa only [interior_Icc] using hq
    have hsin : Real.sin (s - q) ≤ 0 := by
      have hnon : s - q ≤ 0 := by linarith [hsa, hi.1]
      have hnegpi : -Real.pi ≤ s - q := by
        have hqT : q ≤ T := le_trans (le_of_lt hi.2) hbT
        have hqs : q - s ≤ T := by linarith
        nlinarith [T_le_pi]
      exact Real.sin_nonpos_of_nonpos_of_neg_pi_le hnon hnegpi
    have heq : dot ((r q) • v q) (u s) = r q * Real.sin (s - q) := by
      simp [dot, u, v, Real.sin_sub]
      ring
    rw [heq]
    exact mul_nonneg_of_nonpos_of_nonpos (hr q hi) hsin

private theorem phaseB_anti_right
    {F : ℝ → Point} {r : ℝ → ℝ} {a b s : ℝ}
    (hder : ∀ q,
      HasDerivAt (fun x => dot (F x) (u s))
        (dot ((r q) • v q) (u s)) q)
    (hr : ∀ q ∈ Ioo a b, r q ≤ 0)
    (ha0 : 0 ≤ a) (hbs : b ≤ s) (hsT : s ≤ T) :
    AntitoneOn (fun q => dot (F q) (u s)) (Icc a b) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos
    (f' := fun q => dot ((r q) • v q) (u s)) (convex_Icc a b) ?_ ?_ ?_
  · intro q hq
    exact (hder q).continuousAt.continuousWithinAt
  · intro q hq
    exact (hder q).hasDerivWithinAt
  · intro q hq
    have hi : q ∈ Ioo a b := by simpa only [interior_Icc] using hq
    have hq0 : 0 ≤ q := le_trans ha0 (le_of_lt hi.1)
    have hdelta0 : 0 ≤ s - q := by linarith [hi.2, hbs]
    have hdeltaPi : s - q ≤ Real.pi := by
      have : s - q ≤ T := by linarith [hsT, hq0]
      exact le_trans this T_le_pi
    have hsin : 0 ≤ Real.sin (s - q) :=
      Real.sin_nonneg_of_nonneg_of_le_pi hdelta0 hdeltaPi
    have heq : dot ((r q) • v q) (u s) = r q * Real.sin (s - q) := by
      simp [dot, u, v, Real.sin_sub]
      ring
    rw [heq]
    exact mul_nonpos_of_nonpos_of_nonneg (hr q hi) hsin

private theorem criticalU_eq_Bdiff (t : ℝ) :
    Stage2.UValue params.phi t = dot (B eta - B t) (u t) := by
  unfold Stage2.UValue
  rw [← B_eta_eq_path_phi]
  have hinner := B_inner_u_identity t
  unfold dot at hinner ⊢
  dsimp at hinner ⊢
  linarith

private theorem phase3_U_phi_nonneg {t : ℝ}
    (ht : t ∈ Icc params.theta eta) :
    0 ≤ Stage2.UValue params.phi t := by
  have hm := phaseB_mono_left (F := phaseB3)
    (r := fun q => params.c1 - q) (a := t) (b := eta) (s := t)
    (phaseB3_dot_hasDerivAt t)
    (by intro q hq; exact phaseB3_coeff_nonpos (le_trans ht.1 (le_of_lt hq.1)))
    (le_trans theta_pos.le ht.1) (le_rfl) eta_lt_T.le
  have hcomp := hm ⟨le_rfl, ht.2⟩ ⟨ht.2, le_rfl⟩ ht.2
  have hBt := B_eq_phaseB3 ht
  have hBe := B_eq_phaseB3 (t := eta) ⟨theta_lt_eta.le, le_rfl⟩
  rw [criticalU_eq_Bdiff, hBt, hBe]
  unfold dot at hcomp ⊢
  dsimp at hcomp ⊢
  linarith

private theorem phase4_U_phi_nonneg {t : ℝ}
    (ht : t ∈ Icc eta tau) :
    0 ≤ Stage2.UValue params.phi t := by
  have hm := phaseB_anti_right (F := phaseB4)
    (r := fun q => params.d1 - q / 2 - 1) (a := eta) (b := t) (s := t)
    (phaseB4_dot_hasDerivAt t)
    (by intro q hq; exact phaseB4_coeff_nonpos (le_of_lt hq.1))
    (le_trans theta_pos.le theta_lt_eta.le) (le_rfl) (le_trans ht.2 tau_lt_T.le)
  have hcomp := hm ⟨le_rfl, ht.1⟩ ⟨ht.1, le_rfl⟩ ht.1
  have hBt := B_eq_phaseB4 ht
  have hBe := B_eq_phaseB4 (t := eta) ⟨le_rfl, eta_lt_tau.le⟩
  rw [criticalU_eq_Bdiff, hBt, hBe]
  unfold dot at hcomp ⊢
  dsimp at hcomp ⊢
  linarith

private theorem phase5_U_phi_nonneg {t : ℝ}
    (ht : t ∈ Icc tau T) :
    0 ≤ Stage2.UValue params.phi t := by
  have hm4 := phaseB_anti_right (F := phaseB4)
    (r := fun q => params.d1 - q / 2 - 1) (a := eta) (b := tau) (s := t)
    (phaseB4_dot_hasDerivAt t)
    (by intro q hq; exact phaseB4_coeff_nonpos (le_of_lt hq.1))
    (le_trans theta_pos.le theta_lt_eta.le) ht.1 ht.2
  have h4 := hm4 ⟨le_rfl, eta_lt_tau.le⟩ ⟨eta_lt_tau.le, le_rfl⟩ eta_lt_tau.le
  have hm5 := phaseB_anti_right (F := phaseB5)
    (r := fun _ => (-(1 / 2 : ℝ))) (a := tau) (b := t) (s := t)
    (phaseB5_dot_hasDerivAt t)
    (by intro q hq; norm_num)
    (le_trans theta_pos.le (lt_trans theta_lt_eta eta_lt_tau).le) (le_rfl) ht.2
  have h5 := hm5 ⟨le_rfl, ht.1⟩ ⟨ht.1, le_rfl⟩ ht.1
  have hBetaEta := B_eq_phaseB4 (t := eta) ⟨le_rfl, eta_lt_tau.le⟩
  have hBetaTau4 := B_eq_phaseB4 (t := tau) ⟨eta_lt_tau.le, le_rfl⟩
  have hBetaTau5 := B_eq_phaseB5 (t := tau) ⟨le_rfl, tau_lt_T.le⟩
  have hBetaT := B_eq_phaseB5 ht
  rw [criticalU_eq_Bdiff, hBetaEta, hBetaT]
  have hmatch : phaseB4 tau = phaseB5 tau := by
    rw [← hBetaTau4, ← hBetaTau5]
  change dot (phaseB4 tau) (u t) ≤ dot (phaseB4 eta) (u t) at h4
  rw [hmatch] at h4
  unfold dot at h4 h5 ⊢
  dsimp at h4 h5 ⊢
  linarith

/-- Fixed-endpoint separation required by the direct no-hidden-crossing proof. -/
theorem U_phi_nonneg {t : ℝ} (ht : t ∈ Icc params.phi T) :
    0 ≤ Stage2.UValue params.phi t := by
  by_cases h2 : t ≤ params.theta
  · exact phase2_U_phi_nonneg ⟨ht.1, h2⟩
  have htheta : params.theta < t := lt_of_not_ge h2
  by_cases h3 : t ≤ eta
  · exact phase3_U_phi_nonneg ⟨htheta.le, h3⟩
  have hetaT : eta < t := lt_of_not_ge h3
  by_cases h4 : t ≤ tau
  · exact phase4_U_phi_nonneg ⟨hetaT.le, h4⟩
  · exact phase5_U_phi_nonneg ⟨(lt_of_not_ge h4).le, ht.2⟩

end Stage4
end PartC
end GerverSofa
