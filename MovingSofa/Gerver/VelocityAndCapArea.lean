import MovingSofa.Gerver.CapIdentification
import MovingSofa.ForMathlib.MeasureTheory.Measure.PlanarTrapezoid

noncomputable section

namespace MovingSofa

theorem gerver_strict_velocity (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (paperGerverVelocityComponents t).1 < 0 ∧ 0 < (paperGerverVelocityComponents t).2 ∧
    inner ℝ (deriv paperGerverPath t) (normalVector (t : Real.Angle)) < 0 ∧
    0 < inner ℝ (deriv paperGerverPath t) (tangentVector (t : Real.Angle)) := by
  open GerverSofa.Romik in
  -- The certified direct parameter vector, its box enclosures and its equations.
  obtain ⟨p, hp⟩ : ∃ p : Params, GerverSofa.PartB.params = p := ⟨_, rfl⟩
  have hmem : p ∈ gerverDirectBox := hp ▸ GerverSofa.PartB.params_mem
  have heqs : gerverDirectEquations p := hp ▸ GerverSofa.PartB.params_equations
  obtain ⟨-, hphieq, hthetaeq, hphipos, -, -, -⟩ :=
    gerver_parameter_identification.1 p hmem heqs
  have hphi' : p.phi = GerversSofa.φ := hphieq.trans selected_phi
  have htheta' : p.theta = GerversSofa.θ := hthetaeq.trans selected_theta
  have hphi0 : (0 : ℝ) < p.phi := by rw [hphieq]; exact hphipos
  have ha2 : p.a2 = -(1 / 4 : ℝ) := a2_eq_neg_quarter_of_equations heqs
  have he1 : p.e1 = p.a1 := e1_eq_a1_of_equations heqs
  have he2 : p.e2 = -p.a2 := e2_eq_neg_a2_of_equations heqs
  have hbox : p ∈ GerverSofa.Romik.box := hmem
  dsimp only [GerverSofa.Romik.box, GerverSofa.qR, Set.mem_ofPred_eq] at hbox
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      ha1lo, -, -, -, hb1lo, hb1hi, hb2lo, -, hc1lo, -, hc2lo, -, hd1lo, -, hd2lo, -,
      -, -, -, -, -, hphihi, -, hthetahi⟩ := hbox
  have ha1 : (6 : ℝ) / 5 ≤ p.a1 := le_trans (by norm_num) ha1lo
  have hb1u : p.b1 ≤ -(1 / 2 : ℝ) := le_trans hb1hi (by norm_num)
  have hb1l : -(53 / 100 : ℝ) ≤ p.b1 := le_trans (by norm_num) hb1lo
  have hb2 : (9 : ℝ) / 10 ≤ p.b2 := le_trans (by norm_num) hb2lo
  have hc1 : (3 : ℝ) / 5 ≤ p.c1 := le_trans (by norm_num) hc1lo
  have hc2 : (-1 : ℝ) ≤ p.c2 := le_trans (by norm_num) hc2lo
  have hd1 : (13 : ℝ) / 10 ≤ p.d1 := le_trans (by norm_num) hd1lo
  have hd2 : -(53 / 100 : ℝ) ≤ p.d2 := le_trans (by norm_num) hd2lo
  have hphiu : p.phi ≤ (1 : ℝ) / 20 := le_trans hphihi (by norm_num)
  have hthetau : p.theta ≤ (7 : ℝ) / 10 := le_trans hthetahi (by norm_num)
  have hpilo : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpihi : Real.pi < (63 : ℝ) / 20 := by linarith only [Real.pi_lt_d2]
  -- The two strict first-phase estimates, also used on the reflected fifth phase.
  have hkeyA : ∀ s : ℝ, 0 ≤ s → s ≤ (1 : ℝ) / 20 →
      (alphaBeta1 p s).1 ≤ -(2 * s) := by
    intro s hs0 hs20
    have hspi : s ≤ Real.pi := by linarith only [hs20, hpilo]
    have hsin0 : 0 ≤ Real.sin s := Real.sin_nonneg_of_nonneg_of_le_pi hs0 hspi
    have hsinlo : s - s ^ 3 / 6 ≤ Real.sin s := Real.sin_ge_sub_cube hs0
    have hcoslo : 1 - s ^ 2 / 2 ≤ Real.cos s := Real.one_sub_sq_div_two_le_cos
    have hmul : (12 / 5 : ℝ) * Real.sin s ≤ 2 * p.a1 * Real.sin s := by
      nlinarith only [ha1, hsin0]
    have hquad : 0 ≤ s * ((1 / 20 : ℝ) - s) := mul_nonneg hs0 (by linarith only [hs20])
    have hcube : 0 ≤ s ^ 2 * ((1 / 20 : ℝ) - s) :=
      mul_nonneg (sq_nonneg s) (by linarith only [hs20])
    dsimp [alphaBeta1]
    rw [ha2]
    linarith only [hmul, hsinlo, hcoslo, hquad, hcube, hs0]
  have hkeyB : ∀ s : ℝ, 0 ≤ s → s ≤ (1 : ℝ) / 20 →
      (343 : ℝ) / 250 ≤ (alphaBeta1 p s).2 := by
    intro s hs0 hs20
    have hspi : s ≤ Real.pi := by linarith only [hs20, hpilo]
    have hsinhi : Real.sin s ≤ s := Real.sin_le hs0
    have hcoslo : 1 - s ^ 2 / 2 ≤ Real.cos s := Real.one_sub_sq_div_two_le_cos
    have hcos0 : 0 ≤ Real.cos s :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith only [hs0, hpilo], by linarith only [hs20, hpilo]⟩
    have hmul : (12 / 5 : ℝ) * Real.cos s ≤ 2 * p.a1 * Real.cos s := by
      nlinarith only [ha1, hcos0]
    have hquad : 0 ≤ s * ((1 / 20 : ℝ) - s) := mul_nonneg hs0 (by linarith only [hs20])
    dsimp [alphaBeta1]
    rw [ha2]
    linarith only [hmul, hsinhi, hcoslo, hquad, hs0, hs20]
  -- The fifth phase is the reflection of the first one through the angle `π/4`.
  have hrefl : ∀ s : ℝ, alphaBeta5 p (Real.pi / 2 - s) =
      (-(alphaBeta1 p s).2, -(alphaBeta1 p s).1) := by
    intro s
    dsimp [alphaBeta5, alphaBeta1]
    rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub, he1, he2]
    simp only [Prod.mk.injEq]
    constructor <;> ring
  -- The five closed stage intervals in terms of the direct switching angles.
  have hI0 : gerverStageIntervals 0 = Set.Icc 0 p.phi := by
    simp [gerverStageIntervals, gerverStageTimes, hphi']
  have hI1 : gerverStageIntervals 1 = Set.Icc p.phi p.theta := by
    simp [gerverStageIntervals, gerverStageTimes, hphi', htheta']
  have hI2 : gerverStageIntervals 2 = Set.Icc p.theta (Real.pi / 2 - p.theta) := by
    simp [gerverStageIntervals, gerverStageTimes, htheta']
  have hI3 : gerverStageIntervals 3 =
      Set.Icc (Real.pi / 2 - p.theta) (Real.pi / 2 - p.phi) := by
    simp [gerverStageIntervals, gerverStageTimes, hphi', htheta']
  have hI4 : gerverStageIntervals 4 = Set.Icc (Real.pi / 2 - p.phi) (Real.pi / 2) := by
    simp [gerverStageIntervals, gerverStageTimes, hphi']
  have hval := paperGerverContactData_properties.2.2.2
  have hmain : (paperGerverVelocityComponents t).1 < 0 ∧
      0 < (paperGerverVelocityComponents t).2 := by
    rcases le_or_gt t p.phi with hs1 | hs1
    · -- Phase 1: `α ≤ -2t < 0` and `β ≥ 343/250 > 0`.
      have hv : paperGerverVelocityComponents t = alphaBeta1 p t := by
        rw [hval 0 t (by rw [hI0]; exact ⟨ht.1.le, hs1⟩)]
        simp [gerverBranchVelocityComponents, hp]
      have htu : t ≤ (1 : ℝ) / 20 := le_trans hs1 hphiu
      rw [hv]
      exact ⟨by linarith only [hkeyA t ht.1.le htu, ht.1],
        by linarith only [hkeyB t ht.1.le htu]⟩
    rcases le_or_gt t p.theta with hs2 | hs2
    · -- Phase 2: `α ≤ -t < 0` and `β ≥ 1813/2000 > 0`.
      have hv : paperGerverVelocityComponents t = alphaBeta2 p t := by
        rw [hval 1 t (by rw [hI1]; exact ⟨hs1.le, hs2⟩)]
        simp [gerverBranchVelocityComponents, hp]
      have htu : t ≤ (7 : ℝ) / 10 := le_trans hs2 hthetau
      have hbt : 0 ≤ (p.b1 + 53 / 100) * t := mul_nonneg (by linarith only [hb1l]) ht.1.le
      have hst : 0 ≤ ((7 : ℝ) / 10 - t) * t := mul_nonneg (by linarith only [htu]) ht.1.le
      rw [hv]
      dsimp [alphaBeta2]
      exact ⟨by linarith only [hb1u, ht.1], by linarith only [hb2, hbt, hst, htu]⟩
    rcases le_or_gt t (Real.pi / 2 - p.theta) with hs3 | hs3
    · -- Phase 3: `α ≤ -t < 0` and `β ≥ 8/5 - t > 0`.
      have hv : paperGerverVelocityComponents t = alphaBeta3 p t := by
        rw [hval 2 t (by rw [hI2]; exact ⟨hs2.le, hs3⟩)]
        simp [gerverBranchVelocityComponents, hp]
      rw [hv]
      dsimp [alphaBeta3]
      exact ⟨by linarith only [hc2, ht.1], by linarith only [hc1, ht.2, hpihi]⟩
    rcases le_or_gt t (Real.pi / 2 - p.phi) with hs4 | hs4
    · -- Phase 4: `-α > 69/100 > 0` and `β ≥ 8/5 - t > 0`.
      have hv : paperGerverVelocityComponents t = alphaBeta4 p t := by
        rw [hval 3 t (by rw [hI3]; exact ⟨hs3.le, hs4⟩)]
        simp [gerverBranchVelocityComponents, hp]
      have htlo : (4 : ℝ) / 5 < t := by linarith only [hs3, hthetau, hpilo]
      have hthi : t < (8 : ℝ) / 5 := by linarith only [ht.2, hpihi]
      have hcoef : (9 : ℝ) / 10 ≤ p.d1 - t / 4 := by linarith only [hd1, hthi]
      have hprod : (18 : ℝ) / 25 < t * (p.d1 - t / 4) := by nlinarith only [htlo, hcoef]
      rw [hv]
      dsimp [alphaBeta4]
      exact ⟨by linarith only [hprod, hd2], by linarith only [hd1, hthi]⟩
    · -- Phase 5: the reflected first-phase estimates at `s = π/2 - t ∈ (0, φ]`.
      have hv : paperGerverVelocityComponents t = alphaBeta5 p t := by
        rw [hval 4 t (by rw [hI4]; exact ⟨hs4.le, ht.2.le⟩)]
        simp [gerverBranchVelocityComponents, hp]
      have hs0 : 0 < Real.pi / 2 - t := by linarith only [ht.2]
      have hsu : Real.pi / 2 - t ≤ (1 : ℝ) / 20 := by linarith only [hs4, hphiu]
      have hA := hkeyA (Real.pi / 2 - t) hs0.le hsu
      have hB := hkeyB (Real.pi / 2 - t) hs0.le hsu
      have h5 := hrefl (Real.pi / 2 - t)
      rw [show Real.pi / 2 - (Real.pi / 2 - t) = t by ring] at h5
      have hfst : (alphaBeta5 p t).1 = -(alphaBeta1 p (Real.pi / 2 - t)).2 := by rw [h5]
      have hsnd : (alphaBeta5 p t).2 = -(alphaBeta1 p (Real.pi / 2 - t)).1 := by rw [h5]
      rw [hv, hfst, hsnd]
      exact ⟨by linarith only [hB], by linarith only [hA, hs0]⟩
  exact ⟨hmain.1, hmain.2, hmain.1, hmain.2⟩

/-- The tangential velocity component is nonpositive on the whole closed rotation interval:
the strict inequality of `gerver_strict_velocity` holds on the open interval, and the
component is continuous, so the closed condition propagates to the two endpoints. -/
theorem paperGerverVelocityComponents_fst_nonpos {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) : (paperGerverVelocityComponents t).1 ≤ 0 := by
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  have hcl : IsClosed {s : ℝ | (paperGerverVelocityComponents s).1 ≤ 0} :=
    isClosed_le (continuous_fst.comp paperGerverContactData_properties.1) continuous_const
  have h := closure_minimal
    (fun s hs => (gerver_strict_velocity s hs).1.le : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ _) hcl
  rw [closure_Ioo hpi.ne] at h
  exact h ht

/-- The normal velocity component is nonnegative on the whole closed rotation interval; see
`paperGerverVelocityComponents_fst_nonpos` for the argument. -/
theorem paperGerverVelocityComponents_snd_nonneg {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) : 0 ≤ (paperGerverVelocityComponents t).2 := by
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  have hcl : IsClosed {s : ℝ | 0 ≤ (paperGerverVelocityComponents s).2} :=
    isClosed_le continuous_const (continuous_snd.comp paperGerverContactData_properties.1)
  have h := closure_minimal
    (fun s hs => (gerver_strict_velocity s hs).2.1.le : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ _) hcl
  rw [closure_Ioo hpi.ne] at h
  exact h ht

theorem gerver_cap_area_lower_bound :
    2 * GerverSofa.PartB.params.a1 ≤ ClassicalResults.area gerverOuterCap ∧
    (12 : ℝ) / 5 ≤ 2 * GerverSofa.PartB.params.a1 ∧ (11 : ℝ) / 5 < 12 / 5 := by
  open GerverSofa.Romik in
  -- The certified direct parameter vector, its box enclosures and its equations.
  obtain ⟨p, hp⟩ : ∃ p : Params, GerverSofa.PartB.params = p := ⟨_, rfl⟩
  rw [hp]
  have hmem : p ∈ gerverDirectBox := hp ▸ GerverSofa.PartB.params_mem
  have heqs : gerverDirectEquations p := hp ▸ GerverSofa.PartB.params_equations
  obtain ⟨-, hphieq, hthetaeq, hphipos, hphitheta, hthetalt, -⟩ :=
    gerver_parameter_identification.1 p hmem heqs
  have hphi' : p.phi = GerversSofa.φ := hphieq.trans selected_phi
  have h0 : (0 : ℝ) < p.phi := by rw [hphieq]; exact hphipos
  have h1 : p.phi < p.theta := by rw [hphieq, hthetaeq]; exact hphitheta
  have h2 : p.theta < Real.pi / 4 := by rw [hthetaeq]; exact hthetalt
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hbox : p ∈ GerverSofa.Romik.box := hmem
  dsimp only [GerverSofa.Romik.box, GerverSofa.qR, Set.mem_ofPred_eq] at hbox
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hk51lo, hk51hi, -, -,
      ha1lo, ha1hi, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, -, -, -, -, -⟩ := hbox
  have ha1 : (6 : ℝ) / 5 ≤ p.a1 := le_trans (by norm_num) ha1lo
  have ha1' : p.a1 ≤ (61 : ℝ) / 50 := le_trans ha1hi (by norm_num)
  have hk51 : -(51 : ℝ) / 50 ≤ p.k51 := le_trans (by norm_num) hk51lo
  have hk51' : p.k51 ≤ -1 := le_trans hk51hi (by norm_num)
  have ha2 : p.a2 = -(1 / 4 : ℝ) := a2_eq_neg_quarter_of_equations heqs
  have he1 : p.e1 = p.a1 := e1_eq_a1_of_equations heqs
  have he2 : p.e2 = -p.a2 := e2_eq_neg_a2_of_equations heqs
  have hk52 : p.k52 = (1 / 4 : ℝ) := k52_eq_quarter_of_equations heqs
  -- The two path endpoints: `x(0) = 0` and `x(π/2) = (1 - a₁ + k₅₁, 0)`.
  obtain ⟨-, hzero, -⟩ := gerver_direct_path_regularity p hmem heqs
  have hpath0 : paperGerverPath 0 = 0 := by
    show GerverSofa.PartF.Coordinates.toPlane (path GerverSofa.PartB.params 0) = 0
    rw [hp, hzero]
    ext i
    fin_cases i <;> rfl
  have hpathT : path p (Real.pi / 2) = (1 - p.a1 + p.k51, 0) := by
    rw [path_eq_path5_of_mem_Icc heqs h1 h2 ⟨by linarith, le_rfl⟩]
    simp only [path5, addK, rot, Real.cos_pi_div_two, Real.sin_pi_div_two, he1, he2, ha2, hk52,
      Prod.mk.injEq]
    constructor <;> ring
  have hxT0 : paperGerverPath (Real.pi / 2) 0 = 1 - p.a1 + p.k51 := by
    show (path GerverSofa.PartB.params (Real.pi / 2)).1 = _
    rw [hp, hpathT]
  have hxT1 : paperGerverPath (Real.pi / 2) 1 = 0 := by
    show (path GerverSofa.PartB.params (Real.pi / 2)).2 = _
    rw [hp, hpathT]
  -- The velocity components at the two endpoints.
  have hvel := paperGerverContactData_properties.2.2.2
  have hI0 : gerverStageIntervals 0 = Set.Icc 0 p.phi := by
    simp [gerverStageIntervals, gerverStageTimes, hphi']
  have hI4 : gerverStageIntervals 4 = Set.Icc (Real.pi / 2 - p.phi) (Real.pi / 2) := by
    simp [gerverStageIntervals, gerverStageTimes, hphi']
  have halpha0 : (paperGerverVelocityComponents 0).1 = 0 := by
    rw [hvel 0 0 (by rw [hI0]; exact ⟨le_rfl, h0.le⟩)]
    simp [gerverBranchVelocityComponents, hp, alphaBeta1, ha2]
    norm_num
  have hbeta0 : (paperGerverVelocityComponents 0).2 = 2 * p.a1 - 1 := by
    rw [hvel 0 0 (by rw [hI0]; exact ⟨le_rfl, h0.le⟩)]
    simp [gerverBranchVelocityComponents, hp, alphaBeta1, ha2]
  have halphaT : (paperGerverVelocityComponents (Real.pi / 2)).1 = 1 - 2 * p.a1 := by
    rw [hvel 4 (Real.pi / 2) (by rw [hI4]; exact ⟨by linarith, le_rfl⟩)]
    simp [gerverBranchVelocityComponents, hp, alphaBeta5, he1]
  have hbetaT : (paperGerverVelocityComponents (Real.pi / 2)).2 = 0 := by
    rw [hvel 4 (Real.pi / 2) (by rw [hI4]; exact ⟨by linarith, le_rfl⟩)]
    simp [gerverBranchVelocityComponents, hp, alphaBeta5, he2, ha2]
    norm_num
  -- The four displayed cap contacts, in coordinates.
  have hpteq : ∀ z w : Point, z 0 = w 0 → z 1 = w 1 → z = w := by
    intro z w hz hw
    ext i
    fin_cases i
    · exact hz
    · exact hw
  have hA0 : paperGerverContacts 0 0 = (!₂[1, 0] : Point) := by
    refine hpteq _ _ ?_ ?_ <;>
      simp [paperGerverContacts, normalVector, tangentVector, frame, halpha0, hpath0]
  have hC0 : paperGerverContacts 0 2 = (!₂[1 - 2 * p.a1, 1] : Point) := by
    refine hpteq _ _ ?_ ?_ <;>
      simp [paperGerverContacts, normalVector, tangentVector, frame, hbeta0, hpath0]
  have hAT : paperGerverContacts (Real.pi / 2) 0 = (!₂[p.a1 + p.k51, 1] : Point) := by
    refine hpteq _ _ ?_ ?_ <;>
      simp [paperGerverContacts, normalVector, tangentVector, frame, halphaT, hxT0, hxT1]
    ring
  have hCT : paperGerverContacts (Real.pi / 2) 2 = (!₂[p.k51 - p.a1, 0] : Point) := by
    refine hpteq _ _ ?_ ?_ <;>
      simp [paperGerverContacts, normalVector, tangentVector, frame, hbetaT, hxT0, hxT1]
    ring
  -- The cap is a convex body, so it is convex and of finite area.
  obtain ⟨-, -, -, -, -, ⟨K, hKset, -⟩, -⟩ := gerver_capSupport_identification
  have hconv : Convex ℝ gerverOuterCap := hKset ▸ K.val.convex'
  have hcomp : IsCompact gerverOuterCap := hKset ▸ K.val.isCompact'
  -- The inscribed trapezoid and its area.
  have hsub := EuclideanSpace.horizontalTrapezoid_subset_of_convex hconv
    (l₀ := p.k51 - p.a1) (r₀ := 1) (l₁ := 1 - 2 * p.a1) (r₁ := p.a1 + p.k51)
    (hCT ▸ gerver_outer_contact_C (Real.pi / 2) ⟨by positivity, le_rfl⟩)
    (hA0 ▸ gerver_outer_contact_A 0 ⟨le_rfl, by positivity⟩)
    (hC0 ▸ gerver_outer_contact_C 0 ⟨le_rfl, by positivity⟩)
    (hAT ▸ gerver_outer_contact_A (Real.pi / 2) ⟨by positivity, le_rfl⟩)
  have hvol := EuclideanSpace.volume_horizontalTrapezoid (l₀ := p.k51 - p.a1) (r₀ := 1)
    (l₁ := 1 - 2 * p.a1) (r₁ := p.a1 + p.k51) (by linarith) (by linarith)
  have hkey : ENNReal.ofReal (2 * p.a1) ≤ MeasureTheory.volume gerverOuterCap := by
    rw [show (2 * p.a1 : ℝ) =
      (1 - (p.k51 - p.a1) + (p.a1 + p.k51 - (1 - 2 * p.a1))) / 2 by ring, ← hvol]
    exact MeasureTheory.measure_mono hsub
  refine ⟨?_, by linarith, by norm_num⟩
  rw [ClassicalResults.area]
  exact (ENNReal.ofReal_le_iff_le_toReal hcomp.measure_lt_top.ne).1 hkey

end MovingSofa
