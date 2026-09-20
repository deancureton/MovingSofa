import MovingSofa.Gerver.CapIdentification
import MovingSofa.Cap.Tail.Space
import MovingSofa.Analysis.SurfaceMeasure.AngularDensity
import MovingSofa.ForMathlib.MeasureTheory.Measure.Atoms

/-!
# Surface densities of the certified Gerver cap

The certified Gerver cap carries the two envelope densities `GerverSofa.PartC.Stage2.rhoA` and
`rhoC` of the vendor development: its surface-area measure is `rhoA (t) dt` on the angular arc
`[0, π/2)` and `rhoC (t - π/2) dt` on `(π/2, π]`.

The argument is stage by stage.  On each of the five closed stages the selected (positive) vertex
of the cap is a globally analytic branch of the certified phase curves, with derivative
`rhoA t • v t` for the first contact and `-rhoC t • u t` for the third, so
`surfaceAreaMeasure_angleImage_eq_withDensity_of_hasDerivAt` identifies the surface measure with
the exact Lebesgue density on that stage.  The stages are then glued with
`measure_angleImage_eq_of_union`; only the last `rhoA` stage needs an interior exhaustion,
because the positive vertex jumps at `π/2`.

The same stagewise phase curves describe the two *inner* contacts, because `B = A - u` and
`D = C - v` differ from the outer contacts by a frame vector
(`paperGerverContacts_one_eq_sub`, `paperGerverContacts_three_eq_sub`).  Subtracting the frame
vector from a phase curve therefore produces a globally differentiable branch curve for `B` on
the last two stages and for `D` on the first two, with the nonnegative speeds `1 - rhoA` and
`1 - rhoC` (`exists_branch_paperGerverContacts_one`,
`exists_branch_paperGerverContacts_three`); the two speed bounds are again coarse box bounds on
the certified parameters.
-/

noncomputable section

open scoped NNReal

namespace MovingSofa

open MeasureTheory Set
open scoped ENNReal

/-! ### Coordinate transport of derivatives -/

/-- The vendor coordinate identification is homogeneous. -/
private theorem toPlane_smul (c : ℝ) (q : GerverSofa.Point) :
    GerverSofa.PartF.Coordinates.toPlane (c • q) =
      c • GerverSofa.PartF.Coordinates.toPlane q := by
  ext i
  fin_cases i <;> rfl

/-! ### The certified switching angles -/

/-- The paper's two switching angles are the vendor parameter angles, strictly ordered. -/
private theorem paperGerver_switchAngles :
    GerverSofa.PartB.params.phi = GerversSofa.φ ∧
      GerverSofa.PartB.params.theta = GerversSofa.θ ∧
      GerverSofa.PartB.params.phi < GerverSofa.PartB.params.theta ∧
      GerverSofa.PartB.params.theta < Real.pi / 4 := by
  obtain ⟨-, hphi, htheta, -, hphitheta, hthetalt, -⟩ :=
    gerver_parameter_identification.1 GerverSofa.PartB.params GerverSofa.PartB.params_mem
      GerverSofa.PartB.params_equations
  have hphi' : GerverSofa.PartB.params.phi = GerversSofa.φ := hphi.trans selected_phi
  have htheta' : GerverSofa.PartB.params.theta = GerversSofa.θ := htheta.trans selected_theta
  refine ⟨hphi', htheta', ?_, ?_⟩
  · rw [hphi', htheta']; exact hphitheta
  · rw [htheta']; exact hthetalt

/-! ### The contact curves as transported certified phase curves -/

/-- The first contact of the paper Gerver cap is the transported point `x + α v + u`. -/
private theorem paperGerverContacts_zero_eq_toPlane {X W : ℝ → GerverSofa.Point} {t : ℝ}
    (hx : GerverSofa.Romik.path GerverSofa.PartB.params t = X t)
    (hw : paperGerverVelocityComponents t = W t) :
    paperGerverContacts t 0 =
      GerverSofa.PartF.Coordinates.toPlane (X t + (W t).1 • GerverSofa.v t + GerverSofa.u t) := by
  have hp : paperGerverPath t = GerverSofa.PartF.Coordinates.toPlane (X t) := by
    show GerverSofa.PartF.Coordinates.toPlane
      (GerverSofa.Romik.path GerverSofa.PartB.params t) = _
    rw [hx]
  simp only [paperGerverContacts, Matrix.cons_val_zero, hw, hp]
  ext i
  fin_cases i <;> rfl

/-- The third contact of the paper Gerver cap is the transported point `x - β u + v`. -/
private theorem paperGerverContacts_two_eq_toPlane {X W : ℝ → GerverSofa.Point} {t : ℝ}
    (hx : GerverSofa.Romik.path GerverSofa.PartB.params t = X t)
    (hw : paperGerverVelocityComponents t = W t) :
    paperGerverContacts t 2 =
      GerverSofa.PartF.Coordinates.toPlane (X t - (W t).2 • GerverSofa.u t + GerverSofa.v t) := by
  have hp : paperGerverPath t = GerverSofa.PartF.Coordinates.toPlane (X t) := by
    show GerverSofa.PartF.Coordinates.toPlane
      (GerverSofa.Romik.path GerverSofa.PartB.params t) = _
    rw [hx]
  simp only [paperGerverContacts, hw, hp]
  ext i
  fin_cases i <;> rfl

open GerverSofa.PartC.Stage2 GerverSofa.Romik in
/-- On each of the five stages the two contact curves are transported analytic phase curves whose
derivatives are `rA • v` and `-rC • u` for continuous factors agreeing with `rhoA`, `rhoC`. -/
private theorem exists_phaseCurves_of_stage (j : Fin 5) :
    ∃ (PA PC : ℝ → GerverSofa.Point) (rA rC : ℝ → ℝ),
      (∀ t, HasDerivAt PA (rA t • GerverSofa.v t) t) ∧
      (∀ t, HasDerivAt PC (-(rC t) • GerverSofa.u t) t) ∧
      Continuous rA ∧ Continuous rC ∧
      (∀ t ∈ gerverStageIntervals j,
        paperGerverContacts t 0 = GerverSofa.PartF.Coordinates.toPlane (PA t) ∧
        paperGerverContacts t 2 = GerverSofa.PartF.Coordinates.toPlane (PC t)) ∧
      (∀ t ∈ Set.Ioc (gerverStageTimes j.castSucc) (gerverStageTimes j.succ),
        rhoA t = rA t ∧ rhoC t = rC t) := by
  classical
  obtain ⟨hphi', htheta', hφθ', hθq'⟩ := paperGerver_switchAngles
  have heqs : Equations GerverSofa.PartB.params := GerverSofa.PartB.params_equations
  have hφθ : GerversSofa.φ < GerversSofa.θ := by rw [← hphi', ← htheta']; exact hφθ'
  have hθq : GerversSofa.θ < Real.pi / 4 := by rw [← htheta']; exact hθq'
  have hθη : GerversSofa.θ ≤ Real.pi / 2 - GerversSofa.θ := by
    have := GerverSofa.PartC.switchOrder.theta_le_eta
    rw [htheta'] at this; exact this
  have hητ : Real.pi / 2 - GerversSofa.θ ≤ Real.pi / 2 - GerversSofa.φ := by linarith
  have heta : GerverSofa.PartC.eta = Real.pi / 2 - GerversSofa.θ := by
    simp only [GerverSofa.PartC.eta, GerverSofa.PartC.T, htheta']
  have htau : GerverSofa.PartC.tau = Real.pi / 2 - GerversSofa.φ := by
    simp only [GerverSofa.PartC.tau, GerverSofa.PartC.T, hphi']
  have hvel : ∀ (i : Fin 5), ∀ t ∈ gerverStageIntervals i,
      paperGerverVelocityComponents t = gerverBranchVelocityComponents i t :=
    paperGerverContactData_properties.2.2.2
  fin_cases j
  · refine ⟨phaseA1, phaseC1, fun _ ↦ 0, fun _ ↦ 1 / 2, fun t ↦ A1_hasDerivAt_public t,
      fun t ↦ C1_hasDerivAt_public t, continuous_const, continuous_const, ?_, ?_⟩
    · show ∀ t ∈ Set.Icc (0 : ℝ) GerversSofa.φ, _
      intro t ht
      have hx : path GerverSofa.PartB.params t = path1 GerverSofa.PartB.params t :=
        path_eq_path1_of_mem_Icc _ (by rw [hphi']; exact ht)
      have hw : paperGerverVelocityComponents t = alphaBeta1 GerverSofa.PartB.params t :=
        hvel 0 t ht
      exact ⟨paperGerverContacts_zero_eq_toPlane hx hw, paperGerverContacts_two_eq_toPlane hx hw⟩
    · show ∀ t ∈ Set.Ioc (0 : ℝ) GerversSofa.φ, _
      intro t ht
      refine ⟨?_, ?_⟩ <;> simp only [rhoA, rhoC, hphi', htheta', heta, htau] <;>
        split_ifs with h1 h2 h3 h4 <;>
        first
          | rfl
          | (exfalso; linarith [ht.1, ht.2, hφθ, hθη, hητ])
  · refine ⟨phaseA2, phaseC2,
      fun t ↦ -(1 / 4 : ℝ) * t * t + GerverSofa.PartC.params.b1 * t +
        GerverSofa.PartC.params.b2 + 1 / 2,
      fun t ↦ t / 2 - GerverSofa.PartC.params.b1,
      fun t ↦ A2_hasDerivAt_public t, fun t ↦ C2_hasDerivAt_public t, by fun_prop, by fun_prop,
      ?_, ?_⟩
    · show ∀ t ∈ Set.Icc GerversSofa.φ GerversSofa.θ, _
      intro t ht
      have hx : path GerverSofa.PartB.params t = path2 GerverSofa.PartB.params t :=
        path_eq_path2_of_mem_Icc heqs (by rw [hphi', htheta']; exact ht)
      have hw : paperGerverVelocityComponents t = alphaBeta2 GerverSofa.PartB.params t :=
        hvel 1 t ht
      exact ⟨paperGerverContacts_zero_eq_toPlane hx hw, paperGerverContacts_two_eq_toPlane hx hw⟩
    · show ∀ t ∈ Set.Ioc GerversSofa.φ GerversSofa.θ, _
      intro t ht
      refine ⟨?_, ?_⟩ <;> simp only [rhoA, rhoC, hphi', htheta', heta, htau] <;>
        split_ifs with h1 h2 h3 h4 <;>
        first
          | rfl
          | (exfalso; linarith [ht.1, ht.2, hφθ, hθη, hητ])
  · refine ⟨phaseA3, phaseC3, fun t ↦ 1 + GerverSofa.PartC.params.c1 - t,
      fun t ↦ 1 + GerverSofa.PartC.params.c2 + t,
      fun t ↦ A3_hasDerivAt_public t, fun t ↦ C3_hasDerivAt_public t, by fun_prop, by fun_prop,
      ?_, ?_⟩
    · show ∀ t ∈ Set.Icc GerversSofa.θ (Real.pi / 2 - GerversSofa.θ), _
      intro t ht
      have hx : path GerverSofa.PartB.params t = path3 GerverSofa.PartB.params t :=
        path_eq_path3_of_mem_Icc heqs hφθ' (by rw [htheta']; exact ht)
      have hw : paperGerverVelocityComponents t = alphaBeta3 GerverSofa.PartB.params t :=
        hvel 2 t ht
      exact ⟨paperGerverContacts_zero_eq_toPlane hx hw, paperGerverContacts_two_eq_toPlane hx hw⟩
    · show ∀ t ∈ Set.Ioc GerversSofa.θ (Real.pi / 2 - GerversSofa.θ), _
      intro t ht
      refine ⟨?_, ?_⟩ <;> simp only [rhoA, rhoC, hphi', htheta', heta, htau] <;>
        split_ifs with h1 h2 h3 h4 <;>
        first
          | rfl
          | (exfalso; linarith [ht.1, ht.2, hφθ, hθη, hητ])
  · refine ⟨phaseA4, phaseC4, fun t ↦ GerverSofa.PartC.params.d1 - t / 2,
      fun t ↦ -(1 / 4 : ℝ) * t * t + GerverSofa.PartC.params.d1 * t +
        GerverSofa.PartC.params.d2 + 1 / 2,
      fun t ↦ A4_hasDerivAt_public t, fun t ↦ C4_hasDerivAt_public t, by fun_prop, by fun_prop,
      ?_, ?_⟩
    · show ∀ t ∈ Set.Icc (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2 - GerversSofa.φ), _
      intro t ht
      have hx : path GerverSofa.PartB.params t = path4 GerverSofa.PartB.params t :=
        path_eq_path4_of_mem_Icc heqs hφθ' hθq' (by rw [hphi', htheta']; exact ht)
      have hw : paperGerverVelocityComponents t = alphaBeta4 GerverSofa.PartB.params t :=
        hvel 3 t ht
      exact ⟨paperGerverContacts_zero_eq_toPlane hx hw, paperGerverContacts_two_eq_toPlane hx hw⟩
    · show ∀ t ∈ Set.Ioc (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2 - GerversSofa.φ), _
      intro t ht
      refine ⟨?_, ?_⟩ <;> simp only [rhoA, rhoC, hphi', htheta', heta, htau] <;>
        split_ifs with h1 h2 h3 h4 <;>
        first
          | rfl
          | (exfalso; linarith [ht.1, ht.2, hφθ, hθη, hητ])
  · refine ⟨phaseA5, phaseC5, fun _ ↦ 1 / 2, fun _ ↦ 0, fun t ↦ A5_hasDerivAt_public t,
      fun t ↦ by simpa using C5_hasDerivAt_public t, continuous_const, continuous_const, ?_, ?_⟩
    · show ∀ t ∈ Set.Icc (Real.pi / 2 - GerversSofa.φ) (Real.pi / 2), _
      intro t ht
      have hx : path GerverSofa.PartB.params t = path5 GerverSofa.PartB.params t :=
        path_eq_path5_of_mem_Icc heqs hφθ' hθq' (by rw [hphi']; exact ht)
      have hw : paperGerverVelocityComponents t = alphaBeta5 GerverSofa.PartB.params t :=
        hvel 4 t ht
      exact ⟨paperGerverContacts_zero_eq_toPlane hx hw, paperGerverContacts_two_eq_toPlane hx hw⟩
    · show ∀ t ∈ Set.Ioc (Real.pi / 2 - GerversSofa.φ) (Real.pi / 2), _
      intro t ht
      refine ⟨?_, ?_⟩ <;> simp only [rhoA, rhoC, hphi', htheta', heta, htau] <;>
        split_ifs with h1 h2 h3 h4 <;>
        first
          | rfl
          | (exfalso; linarith [ht.1, ht.2, hφθ, hθη, hητ])

/-! ### Contact derivatives on the open stages -/

/-- A branch curve agreeing with a global curve on a closed stage computes the global derivative
at every interior parameter of that stage. -/
theorem hasDerivAt_of_eqOn_stage {G F : ℝ → Point} {w : ℝ → Point} {i : Fin 5}
    (hF : ∀ s, HasDerivAt F (w s) s) (hGF : ∀ t ∈ gerverStageIntervals i, G t = F t)
    {t : ℝ} (ht : t ∈ Set.Ioo (gerverStageTimes i.castSucc) (gerverStageTimes i.succ)) :
    HasDerivAt G (w t) t :=
  (hF t).congr_of_eventuallyEq (Filter.eventuallyEq_of_mem (Ioo_mem_nhds ht.1 ht.2)
    fun u hu ↦ hGF u (Set.Ioo_subset_Icc_self hu))

/-- The transported phase curves of a stage are differentiable everywhere, with the two branch
speeds against the moving frame. -/
private theorem hasDerivAt_toPlane_phaseCurves {PA PC : ℝ → GerverSofa.Point}
    {rA rC : ℝ → ℝ} (hPA : ∀ t, HasDerivAt PA (rA t • GerverSofa.v t) t)
    (hPC : ∀ t, HasDerivAt PC (-(rC t) • GerverSofa.u t) t) :
    (∀ s, HasDerivAt (fun u ↦ GerverSofa.PartF.Coordinates.toPlane (PA u))
        (rA s • tangentVector (s : Real.Angle)) s) ∧
      ∀ s, HasDerivAt (fun u ↦ GerverSofa.PartF.Coordinates.toPlane (PC u))
        (-(rC s) • normalVector (s : Real.Angle)) s := by
  refine ⟨fun s ↦ ?_, fun s ↦ ?_⟩
  · have h := hasDerivAt_toPlane (hPA s)
    rwa [toPlane_smul] at h
  · have h := hasDerivAt_toPlane (hPC s)
    rwa [toPlane_smul] at h

/-- Inside each open stage the two contact curves are differentiable with the envelope
densities as their speed factors. -/
private theorem hasDerivAt_paperGerverContacts_of_mem_stage (j : Fin 5) {t : ℝ}
    (ht : t ∈ Set.Ioo (gerverStageTimes j.castSucc) (gerverStageTimes j.succ)) :
    HasDerivAt (fun u ↦ paperGerverContacts u 0)
        (GerverSofa.PartC.Stage2.rhoA t • tangentVector (t : Real.Angle)) t ∧
      HasDerivAt (fun u ↦ paperGerverContacts u 2)
        (-(GerverSofa.PartC.Stage2.rhoC t) • normalVector (t : Real.Angle)) t := by
  obtain ⟨PA, PC, rA, rC, hPA, hPC, -, -, hmem, hrho⟩ := exists_phaseCurves_of_stage j
  obtain ⟨hrA, hrC⟩ := hrho t (Set.Ioo_subset_Ioc_self ht)
  obtain ⟨hA, hC⟩ := hasDerivAt_toPlane_phaseCurves hPA hPC
  refine ⟨?_, ?_⟩
  · rw [hrA]
    exact hasDerivAt_of_eqOn_stage hA (fun u hu ↦ (hmem u hu).1) ht
  · rw [hrC]
    exact hasDerivAt_of_eqOn_stage hC (fun u hu ↦ (hmem u hu).2) ht

/-! ### Singleton faces have no surface atom -/

/-- A face whose positive tangent endpoint does not exceed its negative one carries no surface
atom: the atom is exactly the tangential gap between the two endpoints. -/
private theorem surfaceAreaMeasure_singleton_eq_zero_of_inner_edgeVertices_le
    (K : ConvexBody Point) (t : Real.Angle)
    (h : inner ℝ (edgeVertices K t).1 (tangentVector t) ≤
      inner ℝ (edgeVertices K t).2 (tangentVector t)) :
    surfaceAreaMeasure K {t} = 0 := by
  have hfin : IsFiniteMeasure (surfaceAreaMeasure K) := (surfaceAreaMeasure_face_union K).1
  have hsplit := (surfaceAreaMeasure_atom_length K t).2.2
  have hone : inner ℝ (tangentVector t) (tangentVector t) = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_tangentVector]
    norm_num
  have hinner : inner ℝ (edgeVertices K t).1 (tangentVector t) =
      inner ℝ (edgeVertices K t).2 (tangentVector t) +
        (surfaceAreaMeasure K {t}).toReal := by
    rw [hsplit, inner_add_left, real_inner_smul_left, hone, mul_one]
  have hle : (surfaceAreaMeasure K {t}).toReal ≤ 0 := by linarith
  have hzero : (surfaceAreaMeasure K {t}).toReal = 0 :=
    le_antisymm hle ENNReal.toReal_nonneg
  rcases (ENNReal.toReal_eq_zero_iff _).1 hzero with h0 | htop
  · exact h0
  · exact absurd htop (measure_ne_top _ _)

/-! ### Measurability and boundedness of the two envelope densities -/

private theorem measurable_rhoA : Measurable GerverSofa.PartC.Stage2.rhoA := by
  unfold GerverSofa.PartC.Stage2.rhoA
  refine Measurable.ite measurableSet_Iic measurable_const ?_
  refine Measurable.ite measurableSet_Iic (by fun_prop) ?_
  refine Measurable.ite measurableSet_Iic (by fun_prop) ?_
  exact Measurable.ite measurableSet_Iic (by fun_prop) measurable_const

private theorem measurable_rhoC : Measurable GerverSofa.PartC.Stage2.rhoC := by
  unfold GerverSofa.PartC.Stage2.rhoC
  refine Measurable.ite measurableSet_Iic measurable_const ?_
  refine Measurable.ite measurableSet_Iic (by fun_prop) ?_
  refine Measurable.ite measurableSet_Iic (by fun_prop) ?_
  exact Measurable.ite measurableSet_Iic (by fun_prop) measurable_const

open GerverSofa.PartC.Stage2 in
/-- Each of the finitely many branch polynomials of the two envelope densities is continuous,
hence bounded on the compact physical interval. -/
private theorem exists_bound_rhoA_rhoC : ∃ M : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
    rhoA t ≤ M ∧ rhoC t ≤ M := by
  have key : ∀ f : ℝ → ℝ, Continuous f →
      ∃ M : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2), f t ≤ M := by
    intro f hf
    obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn
      (Set.nonempty_Icc.2 (show (0 : ℝ) ≤ Real.pi / 2 by linarith [Real.pi_pos]))
      hf.continuousOn
    exact ⟨f x, fun t ht ↦ isMaxOn_iff.1 hmax t ht⟩
  obtain ⟨M1, h1⟩ := key (fun t ↦ -(1 / 4 : ℝ) * t * t + GerverSofa.PartC.params.b1 * t +
    GerverSofa.PartC.params.b2 + 1 / 2) (by fun_prop)
  obtain ⟨M2, h2⟩ := key (fun t ↦ 1 + GerverSofa.PartC.params.c1 - t) (by fun_prop)
  obtain ⟨M3, h3⟩ := key (fun t ↦ GerverSofa.PartC.params.d1 - t / 2) (by fun_prop)
  obtain ⟨M4, h4⟩ := key (fun t ↦ t / 2 - GerverSofa.PartC.params.b1) (by fun_prop)
  obtain ⟨M5, h5⟩ := key (fun t ↦ 1 + GerverSofa.PartC.params.c2 + t) (by fun_prop)
  obtain ⟨M6, h6⟩ := key (fun t ↦ -(1 / 4 : ℝ) * t * t + GerverSofa.PartC.params.d1 * t +
    GerverSofa.PartC.params.d2 + 1 / 2) (by fun_prop)
  refine ⟨max (max (max M1 M2) (max M3 M4)) (max (max M5 M6) 1), fun t ht ↦ ⟨?_, ?_⟩⟩
  · rw [rhoA]
    split_ifs
    · exact le_trans (by norm_num) (le_max_right _ _ |>.trans' (le_max_right _ _))
    · exact (h1 t ht).trans (le_max_of_le_left (le_max_of_le_left (le_max_left _ _)))
    · exact (h2 t ht).trans (le_max_of_le_left (le_max_of_le_left (le_max_right _ _)))
    · exact (h3 t ht).trans (le_max_of_le_left (le_max_of_le_right (le_max_left _ _)))
    · exact le_trans (by norm_num) (le_max_of_le_right (le_max_right _ _))
  · rw [rhoC]
    split_ifs
    · exact le_trans (by norm_num) (le_max_of_le_right (le_max_right _ _))
    · exact (h4 t ht).trans (le_max_of_le_left (le_max_of_le_right (le_max_right _ _)))
    · exact (h5 t ht).trans (le_max_of_le_right (le_max_of_le_left (le_max_left _ _)))
    · exact (h6 t ht).trans (le_max_of_le_right (le_max_of_le_left (le_max_right _ _)))
    · exact le_trans (by norm_num) (le_max_of_le_right (le_max_right _ _))

/-! ### Elementary facts about the stage endpoints and the frame -/

/-- The two Gerver switch angles satisfy `0 < φ < θ < π/4`. -/
private theorem gerver_switch_angle_bounds :
    (0 : ℝ) < GerversSofa.φ ∧ GerversSofa.φ < GerversSofa.θ ∧ GerversSofa.θ < Real.pi / 4 := by
  obtain ⟨-, -, -, hpos, hlt, hq, -⟩ :=
    gerver_parameter_identification.1 GerverSofa.PartB.params GerverSofa.PartB.params_mem
      GerverSofa.PartB.params_equations
  refine ⟨selected_phi ▸ hpos, ?_, selected_theta ▸ hq⟩
  rw [← selected_phi, ← selected_theta]
  exact hlt

private theorem gerverStageTimes_nonneg (k : Fin 6) : 0 ≤ gerverStageTimes k := by
  obtain ⟨h0, h1, h2⟩ := gerver_switch_angle_bounds
  have hpi := Real.pi_gt_three
  fin_cases k
  · show (0 : ℝ) ≤ 0
    exact le_refl 0
  · show (0 : ℝ) ≤ GerversSofa.φ
    linarith
  · show (0 : ℝ) ≤ GerversSofa.θ
    linarith
  · show (0 : ℝ) ≤ Real.pi / 2 - GerversSofa.θ
    linarith
  · show (0 : ℝ) ≤ Real.pi / 2 - GerversSofa.φ
    linarith
  · show (0 : ℝ) ≤ Real.pi / 2
    linarith

private theorem gerverStageTimes_le_pi_div_two (k : Fin 6) : gerverStageTimes k ≤ Real.pi / 2 := by
  obtain ⟨h0, h1, h2⟩ := gerver_switch_angle_bounds
  have hpi := Real.pi_gt_three
  fin_cases k
  · show (0 : ℝ) ≤ Real.pi / 2
    linarith
  · show GerversSofa.φ ≤ Real.pi / 2
    linarith
  · show GerversSofa.θ ≤ Real.pi / 2
    linarith
  · show Real.pi / 2 - GerversSofa.θ ≤ Real.pi / 2
    linarith
  · show Real.pi / 2 - GerversSofa.φ ≤ Real.pi / 2
    linarith
  · show Real.pi / 2 ≤ Real.pi / 2
    exact le_refl _

private theorem gerverStageTimes_lt_succ (j : Fin 5) :
    gerverStageTimes j.castSucc < gerverStageTimes j.succ := by
  obtain ⟨h0, h1, h2⟩ := gerver_switch_angle_bounds
  have hpi := Real.pi_gt_three
  fin_cases j
  · show (0 : ℝ) < GerversSofa.φ
    linarith
  · show GerversSofa.φ < GerversSofa.θ
    linarith
  · show GerversSofa.θ < Real.pi / 2 - GerversSofa.θ
    linarith
  · show Real.pi / 2 - GerversSofa.θ < Real.pi / 2 - GerversSofa.φ
    linarith
  · show Real.pi / 2 - GerversSofa.φ < Real.pi / 2
    linarith

private theorem gerverStageTimes_four_lt_pi_div_two : gerverStageTimes 4 < Real.pi / 2 := by
  have h : gerverStageTimes 4 < gerverStageTimes 5 := gerverStageTimes_lt_succ 4
  have h5 : gerverStageTimes 5 = Real.pi / 2 := rfl
  linarith

/-! ### Almost every parameter lies in an open stage -/

/-- A parameter of the rotation interval that is none of the six stage times lies in an open
stage. -/
theorem mem_openStage_of_mem_Ico {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) (Real.pi / 2))
    (hne : ∀ k : Fin 6, t ≠ gerverStageTimes k) :
    ∃ j : Fin 5, t ∈ Set.Ioo (gerverStageTimes j.castSucc) (gerverStageTimes j.succ) := by
  have hlow : gerverStageTimes 0 < t :=
    lt_of_le_of_ne (gerverStageTimes_zero ▸ ht.1) fun h ↦ hne 0 h.symm
  have hhigh : t < gerverStageTimes 5 := ht.2
  rcases lt_or_gt_of_ne (hne 1) with h1 | h1
  · exact ⟨0, hlow, h1⟩
  · rcases lt_or_gt_of_ne (hne 2) with h2 | h2
    · exact ⟨1, h1, h2⟩
    · rcases lt_or_gt_of_ne (hne 3) with h3 | h3
      · exact ⟨2, h2, h3⟩
      · rcases lt_or_gt_of_ne (hne 4) with h4 | h4
        · exact ⟨3, h3, h4⟩
        · exact ⟨4, h4, hhigh⟩

/-- Almost every parameter of a measurable subset of the shifted rotation interval lies in a
shifted open stage. -/
theorem ae_mem_openStage (c : ℝ) {S : Set ℝ} (hS : MeasurableSet S)
    (hSsub : S ⊆ Set.Icc c (c + Real.pi / 2)) :
    ∀ᵐ u ∂volume.restrict S, ∃ j : Fin 5,
      u - c ∈ Set.Ioo (gerverStageTimes j.castSucc) (gerverStageTimes j.succ) := by
  refine ae_restrict_mem_of_countable_diff hS
    (((Set.finite_range gerverStageTimes).countable).image fun x ↦ x + c) ?_
  rintro u ⟨hu, hu'⟩
  by_contra hcon
  have hne : ∀ k : Fin 6, u - c ≠ gerverStageTimes k := by
    intro k hk
    exact hcon ⟨gerverStageTimes k, Set.mem_range_self k, by rw [← hk]; ring⟩
  have hmem : u - c ∈ Set.Ico (0 : ℝ) (Real.pi / 2) := by
    refine ⟨by linarith [(hSsub hu).1], ?_⟩
    have h5 : u - c ≠ gerverStageTimes 5 := hne 5
    rw [show gerverStageTimes 5 = Real.pi / 2 from rfl] at h5
    exact lt_of_le_of_ne (by linarith [(hSsub hu).2]) h5
  exact hu' (mem_openStage_of_mem_Ico hmem hne)

/-! ### Branch curves for the two inner contacts

The second contact `B = x + α v` is the first contact `A = x + α v + u` translated by `-u`, and
the fourth contact `D = x - β u` is the third contact `C = x - β u + v` translated by `-v`.  So
subtracting a frame vector from the transported phase curve of a stage produces a globally
differentiable branch curve for `B` and for `D`, whose speed against the frame is `1 - rhoA`
resp. `1 - rhoC`.  Both are nonnegative exactly where the inner contact is a genuine contact:
after the third stage time for `B` and before the second for `D`.
-/

/-- The second contact curve is the first one translated by `-u_t`. -/
theorem paperGerverContacts_one_eq_sub (t : ℝ) :
    paperGerverContacts t 1 = paperGerverContacts t 0 - normalVector (t : Real.Angle) := by
  show _ = paperGerverPath t + (paperGerverVelocityComponents t).1 •
    tangentVector (t : Real.Angle) + normalVector (t : Real.Angle) - normalVector _
  rw [add_sub_cancel_right]
  rfl

/-- The fourth contact curve is the third one translated by `-v_t`. -/
theorem paperGerverContacts_three_eq_sub (t : ℝ) :
    paperGerverContacts t 3 = paperGerverContacts t 2 - tangentVector (t : Real.Angle) := by
  show _ = paperGerverPath t - (paperGerverVelocityComponents t).2 •
    normalVector (t : Real.Angle) + tangentVector (t : Real.Angle) - tangentVector _
  rw [add_sub_cancel_right]
  rfl

open GerverSofa.PartC.Stage2 in
/-- After the third stage time the first contact never outruns the rotating frame: its tangential
speed `rhoA` is at most the unit speed of `u`.  On the fourth stage this is the coarse bound
`d₁ ≤ 33/25` against `t > π/2 - θ > 4/5`; on the fifth the speed is the constant `1/2`. -/
private theorem rhoA_le_one_of_gerverStageTimes_three_lt {t : ℝ}
    (ht : gerverStageTimes 3 < t) : rhoA t ≤ 1 := by
  have h1 : gerverStageTimes 1 = GerverSofa.PartB.params.phi := gerverStageTimes_one
  have h2 : gerverStageTimes 2 = GerverSofa.PartB.params.theta := gerverStageTimes_two
  have h3 : gerverStageTimes 3 = GerverSofa.PartC.eta := gerverStageTimes_three
  have h4 : gerverStageTimes 4 = GerverSofa.PartC.tau := gerverStageTimes_four
  have h12 : gerverStageTimes 1 < gerverStageTimes 2 := gerverStageTimes_lt_succ 1
  have h23 : gerverStageTimes 2 < gerverStageTimes 3 := gerverStageTimes_lt_succ 2
  have h32 : gerverStageTimes 3 = Real.pi / 2 - gerverStageTimes 2 := rfl
  have hd1 := gerverDirectBox_d1_upper_bound GerverSofa.PartB.params_mem
  have hθ := gerverStageTimes_two_le_seven_div_ten
  have hpi := Real.pi_gt_three
  rw [rhoA]
  split_ifs with hphi htheta heta
  · exact absurd (h1 ▸ hphi) (by linarith)
  · exact absurd (h2 ▸ htheta) (by linarith)
  · exact absurd (h3 ▸ heta) (by linarith)
  · linarith
  · norm_num

open GerverSofa.PartC.Stage2 in
/-- Before the second stage time the third contact never outruns the rotating frame: its normal
speed `rhoC` is at most the unit speed of `v`.  On the first stage the speed is the constant
`1/2`; on the second this is the coarse bound `b₁ ≥ -53/100` against `t ≤ θ ≤ 7/10`. -/
private theorem rhoC_le_one_of_le_gerverStageTimes_two {t : ℝ}
    (ht : t ≤ gerverStageTimes 2) : rhoC t ≤ 1 := by
  have h2 : gerverStageTimes 2 = GerverSofa.PartB.params.theta := gerverStageTimes_two
  have hb1 := gerverDirectBox_b1_lower_bound GerverSofa.PartB.params_mem
  have hθ := gerverStageTimes_two_le_seven_div_ten
  rw [rhoC]
  split_ifs with hphi htheta
  · norm_num
  · linarith
  · exact absurd (h2 ▸ ht) (by linarith)
  · exact absurd (h2 ▸ ht) (by linarith)
  · exact absurd (h2 ▸ ht) (by linarith)

/-- On each of the last two stages the second contact curve agrees with a globally differentiable
branch curve whose derivative is `-(g t) • v_t` for a continuous factor `g` that is nonnegative
on the stage. -/
theorem exists_branch_paperGerverContacts_one {i : Fin 5} (hi : i = 3 ∨ i = 4) :
    ∃ (F : ℝ → Point) (g : ℝ → ℝ),
      (∀ s, HasDerivAt F (-(g s) • tangentVector (s : Real.Angle)) s) ∧ Continuous g ∧
      (∀ t ∈ Set.Ioc (gerverStageTimes i.castSucc) (gerverStageTimes i.succ), 0 ≤ g t) ∧
      (∀ t ∈ gerverStageIntervals i, paperGerverContacts t 1 = F t) := by
  obtain ⟨PA, PC, rA, rC, hPA, hPC, hcA, -, hmem, hrho⟩ := exists_phaseCurves_of_stage i
  obtain ⟨hA, -⟩ := hasDerivAt_toPlane_phaseCurves hPA hPC
  have h3i : gerverStageTimes 3 ≤ gerverStageTimes i.castSucc :=
    gerverStageTimes_strictMono.monotone (by rcases hi with rfl | rfl <;> decide)
  refine ⟨fun s ↦ GerverSofa.PartF.Coordinates.toPlane (PA s) - normalVector (s : Real.Angle),
    fun s ↦ 1 - rA s, fun s ↦ ?_, continuous_const.sub hcA, fun t ht ↦ ?_, fun t ht ↦ ?_⟩
  · refine ((hA s).sub (hasDerivAt_normalVector s)).congr_deriv ?_
    module
  · have hrA := (hrho t ht).1
    linarith [rhoA_le_one_of_gerverStageTimes_three_lt (lt_of_le_of_lt h3i ht.1)]
  · rw [paperGerverContacts_one_eq_sub, (hmem t ht).1]

/-- On each of the first two stages the fourth contact curve agrees with a globally differentiable
branch curve whose derivative is `g t • u_t` for a continuous factor `g` that is nonnegative on
the stage. -/
theorem exists_branch_paperGerverContacts_three {i : Fin 5} (hi : i = 0 ∨ i = 1) :
    ∃ (F : ℝ → Point) (g : ℝ → ℝ),
      (∀ s, HasDerivAt F (g s • normalVector (s : Real.Angle)) s) ∧ Continuous g ∧
      (∀ t ∈ Set.Ioc (gerverStageTimes i.castSucc) (gerverStageTimes i.succ), 0 ≤ g t) ∧
      (∀ t ∈ gerverStageIntervals i, paperGerverContacts t 3 = F t) := by
  obtain ⟨PA, PC, rA, rC, hPA, hPC, -, hcC, hmem, hrho⟩ := exists_phaseCurves_of_stage i
  obtain ⟨-, hC⟩ := hasDerivAt_toPlane_phaseCurves hPA hPC
  have hi2 : gerverStageTimes i.succ ≤ gerverStageTimes 2 :=
    gerverStageTimes_strictMono.monotone (by rcases hi with rfl | rfl <;> decide)
  refine ⟨fun s ↦ GerverSofa.PartF.Coordinates.toPlane (PC s) - tangentVector (s : Real.Angle),
    fun s ↦ 1 - rC s, fun s ↦ ?_, continuous_const.sub hcC, fun t ht ↦ ?_, fun t ht ↦ ?_⟩
  · refine ((hC s).sub (hasDerivAt_tangentVector s)).congr_deriv ?_
    module
  · have hrC := (hrho t ht).2
    linarith [rhoC_le_one_of_le_gerverStageTimes_two (le_trans ht.2 hi2)]
  · rw [paperGerverContacts_three_eq_sub, (hmem t ht).2]

/-! ### The certified cap witness and its positive vertex curves -/

/-- The certified cap witness of support identification, together with the identification of its
positive vertex by the two contact curves on the whole closed parameter interval and the
vanishing of the surface atom at the included endpoint `0`.

Both included endpoint faces are singletons: at `0` the first contact is the anchor `(1, 0)`
and the cap lies in `0 ≤ q 1`, and at `π` the third contact has vanishing second coordinate,
so in each case the positive tangent endpoint cannot exceed the negative one. -/
private theorem exists_gerverCap_positiveVertex :
    ∃ K : CapSpace (Real.pi / 2),
      (K.val : Set Point) = capOfSofa paperGerverSofa (Real.pi / 2) ∧
      surfaceAreaMeasure K.val {((0 : ℝ) : Real.Angle)} = 0 ∧
      (∀ t ∈ Set.Ico (0 : ℝ) (Real.pi / 2),
        (edgeVertices K.val ((t : ℝ) : Real.Angle)).1 = paperGerverContacts t 0) ∧
      (∀ s ∈ Set.Icc (Real.pi / 2) Real.pi,
        (edgeVertices K.val ((s : ℝ) : Real.Angle)).1 =
          paperGerverContacts (s - Real.pi / 2) 2) := by
  have hpi := Real.pi_gt_three
  have hTpos : (0 : ℝ) < Real.pi / 2 := by linarith
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨le_rfl, hTpos.le⟩
  have hTmem : Real.pi / 2 ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨hTpos.le, le_rfl⟩
  obtain ⟨-, hpaper, -, -, hcapEq, ⟨K, hKset, hedges, hA0, -, hC0, hCT⟩, -⟩ :=
    gerver_capSupport_identification
  have hKupper : ∀ q ∈ (K.val : Set Point), 0 ≤ q 1 := by
    intro q hq
    rw [hKset] at hq
    exact hq.1
  -- the two included endpoint contacts lie on the lower fan boundary
  have hcontactA0y : paperGerverContacts 0 0 1 = 0 := by
    have h := fromPlane_paperGerverContacts 0 h0mem 0
    have h2 : paperGerverContacts 0 0 =
        GerverSofa.PartF.Coordinates.toPlane (GerverSofa.PartC.A 0) := by
      rw [← GerverSofa.PartF.Coordinates.toPlane_fromPlane (paperGerverContacts 0 0), h]
      rfl
    rw [h2, GerverSofa.PartC.Stage2.A_zero_eq_anchor]
    rfl
  have hcontactCTy : paperGerverContacts (Real.pi / 2) 2 1 = 0 := by
    have h := fromPlane_paperGerverContacts (Real.pi / 2) hTmem 2
    have h2 : paperGerverContacts (Real.pi / 2) 2 =
        GerverSofa.PartF.Coordinates.toPlane (GerverSofa.PartC.C (Real.pi / 2)) := by
      rw [← GerverSofa.PartF.Coordinates.toPlane_fromPlane
        (paperGerverContacts (Real.pi / 2) 2), h]
      rfl
    rw [h2]
    exact GerverSofa.PartC.Stage2.C_T_snd_zero
  -- hence both included endpoint faces are singletons and carry no atom
  have hatom0 : surfaceAreaMeasure K.val {((0 : ℝ) : Real.Angle)} = 0 := by
    refine surfaceAreaMeasure_singleton_eq_zero_of_inner_edgeVertices_le K.val _ ?_
    have hfst : (edgeVertices K.val ((0 : ℝ) : Real.Angle)).1 = paperGerverContacts 0 0 := by
      rw [Real.Angle.coe_zero]
      exact hA0.symm
    rw [inner_tangentVector_zero, inner_tangentVector_zero, hfst, hcontactA0y]
    exact hKupper _ (edgeVertices_snd_mem K.val _).1
  have hatompi : surfaceAreaMeasure K.val {((Real.pi : ℝ) : Real.Angle)} = 0 := by
    refine surfaceAreaMeasure_singleton_eq_zero_of_inner_edgeVertices_le K.val _ ?_
    rw [inner_tangentVector_pi, inner_tangentVector_pi, ← hCT, hcontactCTy]
    have h := hKupper _ (edgeVertices_fst_mem K.val ((Real.pi : ℝ) : Real.Angle)).1
    linarith
  refine ⟨K, by rw [hpaper, hcapEq]; exact hKset, hatom0, ?_, ?_⟩
  · intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h, Real.Angle.coe_zero]
      exact hA0.symm
    · rw [edgeVertices_eq_of_exposedEdge_singleton (hedges t ⟨h, ht.2⟩).1]
  · intro s hs
    rcases eq_or_lt_of_le hs.1 with h1 | h1
    · rw [← h1, sub_self]
      exact hC0.symm
    rcases eq_or_lt_of_le hs.2 with h2 | h2
    · have hatom := (surfaceAreaMeasure_atom_length K.val ((Real.pi : ℝ) : Real.Angle)).2.2
      rw [hatompi] at hatom
      simp only [ENNReal.toReal_zero, zero_smul, add_zero] at hatom
      rw [h2, show Real.pi - Real.pi / 2 = Real.pi / 2 from by ring, hatom, ← hCT]
    · have htmem : s - Real.pi / 2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
        ⟨by linarith, by linarith⟩
      have h := (hedges (s - Real.pi / 2) htmem).2
      rw [show s - Real.pi / 2 + Real.pi / 2 = s from by ring] at h
      rw [edgeVertices_eq_of_exposedEdge_singleton h]

/-! ### The stagewise density identities -/

/-- On a subinterval of a single stage, strictly below the switch `π/2`, the surface measure of
an angular image is the `rhoA`-weighted Lebesgue measure. -/
private theorem surfaceAreaMeasure_angleImage_eq_withDensity_rhoA_of_stage (K : ConvexBody Point)
    (hvertexA : ∀ t ∈ Set.Ico (0 : ℝ) (Real.pi / 2),
      (edgeVertices K ((t : ℝ) : Real.Angle)).1 = paperGerverContacts t 0)
    (j : Fin 5) (a b : ℝ) (hja : gerverStageTimes j.castSucc ≤ a)
    (hjb : b ≤ gerverStageTimes j.succ) (hbT : b < Real.pi / 2)
    (S : Set ℝ) (hS : MeasurableSet S) (hSsub : S ⊆ Set.Ioc a b) :
    surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
      volume.withDensity (fun s ↦ ENNReal.ofReal (GerverSofa.PartC.Stage2.rhoA s)) S := by
  have hpi := Real.pi_gt_three
  rcases le_or_gt b a with hle | hab
  · have hempty : S = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 fun x hx ↦ ?_
      have hx' := hSsub hx
      rw [Set.mem_Ioc] at hx'
      linarith [hx'.1, hx'.2]
    rw [hempty]
    simp
  obtain ⟨PA, PC, rA, rC, hPA, hPC, hcA, hcC, hmem, hrho⟩ := exists_phaseCurves_of_stage j
  have ha0 : 0 ≤ a := le_trans (gerverStageTimes_nonneg _) hja
  refine surfaceAreaMeasure_angleImage_eq_withDensity_of_hasDerivAt K hab (by linarith)
    (fun s ↦ GerverSofa.PartF.Coordinates.toPlane (PA s)) rA
    GerverSofa.PartC.Stage2.rhoA (fun s ↦ ?_) hcA ?_ ?_ ?_ S hS hSsub
  · have h := hasDerivAt_toPlane (hPA s)
    rw [toPlane_smul] at h
    exact h
  · intro s hs
    rw [hvertexA s ⟨le_trans ha0 hs.1, lt_of_le_of_lt hs.2 hbT⟩]
    exact (hmem s ⟨le_trans hja hs.1, le_trans hs.2 hjb⟩).1
  · intro s hs
    exact (hrho s ⟨lt_of_le_of_lt hja hs.1, le_trans hs.2 hjb⟩).1
  · intro s hs
    have hs0 : (0 : ℝ) ≤ s := by linarith [hs.1]
    have hsT : s ≤ Real.pi / 2 := by linarith [hs.2]
    exact GerverSofa.PartC.Stage2.rhoA_nonneg ⟨hs0, hsT⟩

/-- On a subinterval of a single shifted stage the surface measure of an angular image is the
translated `rhoC`-weighted Lebesgue measure. -/
private theorem surfaceAreaMeasure_angleImage_eq_withDensity_rhoC_of_stage (K : ConvexBody Point)
    (hvertexC : ∀ s ∈ Set.Icc (Real.pi / 2) Real.pi,
      (edgeVertices K ((s : ℝ) : Real.Angle)).1 = paperGerverContacts (s - Real.pi / 2) 2)
    (j : Fin 5) (a b : ℝ) (hja : Real.pi / 2 + gerverStageTimes j.castSucc ≤ a)
    (hjb : b ≤ Real.pi / 2 + gerverStageTimes j.succ)
    (S : Set ℝ) (hS : MeasurableSet S) (hSsub : S ⊆ Set.Ioc a b) :
    surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
      volume.withDensity
        (fun u ↦ ENNReal.ofReal (GerverSofa.PartC.Stage2.rhoC (u - Real.pi / 2))) S := by
  have hpi := Real.pi_gt_three
  rcases le_or_gt b a with hle | hab
  · have hempty : S = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 fun x hx ↦ ?_
      have hx' := hSsub hx
      rw [Set.mem_Ioc] at hx'
      linarith [hx'.1, hx'.2]
    rw [hempty]
    simp
  obtain ⟨PA, PC, rA, rC, hPA, hPC, hcA, hcC, hmem, hrho⟩ := exists_phaseCurves_of_stage j
  have ha0 : Real.pi / 2 ≤ a := le_trans (by linarith [gerverStageTimes_nonneg j.castSucc]) hja
  have hbpi : b ≤ Real.pi := by
    have := gerverStageTimes_le_pi_div_two j.succ
    linarith
  refine surfaceAreaMeasure_angleImage_eq_withDensity_of_hasDerivAt K hab (by linarith)
    (fun s ↦ GerverSofa.PartF.Coordinates.toPlane (PC (s - Real.pi / 2)))
    (fun s ↦ rC (s - Real.pi / 2))
    (fun u ↦ GerverSofa.PartC.Stage2.rhoC (u - Real.pi / 2)) (fun s ↦ ?_)
    (hcC.comp (continuous_id.sub continuous_const)) ?_ ?_ ?_ S hS hSsub
  · have hinner : HasDerivAt (fun x : ℝ ↦ x - Real.pi / 2) 1 s :=
      (hasDerivAt_id s).sub_const _
    have h1 : HasDerivAt (fun x : ℝ ↦ PC (x - Real.pi / 2))
        (-(rC (s - Real.pi / 2)) • GerverSofa.u (s - Real.pi / 2)) s := by
      simpa [Function.comp_def] using (hPC (s - Real.pi / 2)).scomp s hinner
    have h2 := hasDerivAt_toPlane h1
    rw [toPlane_smul] at h2
    have hangle : tangentVector ((s : ℝ) : Real.Angle) =
        -normalVector (((s - Real.pi / 2 : ℝ)) : Real.Angle) := by
      have h := tangentVector_add_pi_div_two (s - Real.pi / 2)
      rw [show s - Real.pi / 2 + Real.pi / 2 = s from by ring] at h
      exact h
    rw [hangle, smul_neg, ← neg_smul]
    exact h2
  · intro s hs
    rw [hvertexC s ⟨le_trans ha0 hs.1, le_trans hs.2 hbpi⟩]
    exact (hmem (s - Real.pi / 2) ⟨by linarith [hs.1], by linarith [hs.2]⟩).2
  · intro s hs
    exact (hrho (s - Real.pi / 2) ⟨by linarith [hs.1], by linarith [hs.2]⟩).2
  · intro s hs
    have hs0 : (0 : ℝ) ≤ s - Real.pi / 2 := by linarith [hs.1]
    have hsT : s - Real.pi / 2 ≤ Real.pi / 2 := by linarith [hs.2, hbpi]
    exact GerverSofa.PartC.Stage2.rhoC_nonneg ⟨hs0, hsT⟩

/-! ### Exhausting the last stage of the first arc from inside -/

/-- The positive vertex jumps at `π/2`, so the last `rhoA` stage is reached by exhausting its
open interval by half-open subintervals. -/
private theorem surfaceAreaMeasure_angleImage_eq_withDensity_rhoA_of_final_stage
    (K : ConvexBody Point)
    (hvertexA : ∀ t ∈ Set.Ico (0 : ℝ) (Real.pi / 2),
      (edgeVertices K ((t : ℝ) : Real.Angle)).1 = paperGerverContacts t 0)
    (S : Set ℝ) (hS : MeasurableSet S) (hSsub : S ⊆ Set.Ioo (gerverStageTimes 4) (Real.pi / 2)) :
    surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
      volume.withDensity (fun s ↦ ENNReal.ofReal (GerverSofa.PartC.Stage2.rhoA s)) S := by
  have h4T := gerverStageTimes_four_lt_pi_div_two
  have hpos : 0 < Real.pi / 2 - gerverStageTimes 4 := by linarith
  have hbnlt : ∀ n : ℕ, Real.pi / 2 -
      (Real.pi / 2 - gerverStageTimes 4) / ((n : ℝ) + 2) < Real.pi / 2 := by
    intro n
    have h : 0 < (Real.pi / 2 - gerverStageTimes 4) / ((n : ℝ) + 2) := by positivity
    linarith
  refine measure_angleImage_eq_of_iUnion
    (J := fun n : ℕ ↦ Set.Ioc (gerverStageTimes 4)
      (Real.pi / 2 - (Real.pi / 2 - gerverStageTimes 4) / ((n : ℝ) + 2)))
    ?_ (fun n ↦ measurableSet_Ioc) ?_ S hS ?_
  · intro m n hmn
    refine Set.Ioc_subset_Ioc_right ?_
    have hmn' : ((m : ℝ) + 2) ≤ ((n : ℝ) + 2) := by
      have : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hmn
      linarith
    have hd : (Real.pi / 2 - gerverStageTimes 4) / ((n : ℝ) + 2) ≤
        (Real.pi / 2 - gerverStageTimes 4) / ((m : ℝ) + 2) := by
      gcongr
    linarith
  · intro n S' hS' hS'sub
    exact surfaceAreaMeasure_angleImage_eq_withDensity_rhoA_of_stage K hvertexA 4 _ _
      (le_refl _) (hbnlt n).le (hbnlt n) S' hS' hS'sub
  · intro x hx
    have hx' := hSsub hx
    obtain ⟨n, hn⟩ := exists_nat_gt ((Real.pi / 2 - gerverStageTimes 4) / (Real.pi / 2 - x))
    refine Set.mem_iUnion.2 ⟨n, ⟨hx'.1, ?_⟩⟩
    have h1 : 0 < Real.pi / 2 - x := by linarith [hx'.2]
    rw [div_lt_iff₀ h1] at hn
    have h4 : (Real.pi / 2 - gerverStageTimes 4) / ((n : ℝ) + 2) < Real.pi / 2 - x := by
      rw [div_lt_iff₀ (by positivity)]
      nlinarith [h1]
    linarith

/-! ### Gluing two adjacent arcs -/

/-- Two adjacent windows inside `[0, π/2]` on which the `rhoA` identity holds may be merged. -/
private theorem surfaceAreaMeasure_angleImage_eq_withDensity_rhoA_of_union (K : ConvexBody Point)
    (x y z : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (hz : z ≤ Real.pi / 2)
    (hI : ∀ S, MeasurableSet S → S ⊆ Set.Icc x y →
      surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
        volume.withDensity (fun s ↦ ENNReal.ofReal (GerverSofa.PartC.Stage2.rhoA s)) S)
    (hJ : ∀ S, MeasurableSet S → S ⊆ Set.Ioc y z →
      surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
        volume.withDensity (fun s ↦ ENNReal.ofReal (GerverSofa.PartC.Stage2.rhoA s)) S)
    (S : Set ℝ) (hS : MeasurableSet S) (hSsub : S ⊆ Set.Icc x z) :
    surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
      volume.withDensity (fun s ↦ ENNReal.ofReal (GerverSofa.PartC.Stage2.rhoA s)) S := by
  have hpi := Real.pi_gt_three
  refine measure_angleImage_eq_of_union (c := -1) (d := Real.pi / 2) (by linarith)
    (I := Set.Icc x y) (J := Set.Ioc y z)
    (fun u hu ↦ ⟨by linarith [hu.1], by linarith [hu.2]⟩)
    (fun u hu ↦ ⟨by linarith [hu.1], by linarith [hu.2]⟩)
    measurableSet_Icc measurableSet_Ioc ?_ hI hJ S hS ?_
  · rw [Set.disjoint_left]
    intro u hu hu'
    linarith [hu.2, hu'.1]
  · rw [Set.Icc_union_Ioc_eq_Icc hxy hyz]
    exact hSsub

/-- Two adjacent windows inside `[π/2, π]` on which the `rhoC` identity holds may be merged. -/
private theorem surfaceAreaMeasure_angleImage_eq_withDensity_rhoC_of_union (K : ConvexBody Point)
    (x y z : ℝ) (hx : Real.pi / 2 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (hz : z ≤ Real.pi)
    (hI : ∀ S, MeasurableSet S → S ⊆ Set.Ioc x y →
      surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
        volume.withDensity
          (fun u ↦ ENNReal.ofReal (GerverSofa.PartC.Stage2.rhoC (u - Real.pi / 2))) S)
    (hJ : ∀ S, MeasurableSet S → S ⊆ Set.Ioc y z →
      surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
        volume.withDensity
          (fun u ↦ ENNReal.ofReal (GerverSofa.PartC.Stage2.rhoC (u - Real.pi / 2))) S)
    (S : Set ℝ) (hS : MeasurableSet S) (hSsub : S ⊆ Set.Ioc x z) :
    surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
      volume.withDensity
        (fun u ↦ ENNReal.ofReal (GerverSofa.PartC.Stage2.rhoC (u - Real.pi / 2))) S := by
  have hpi := Real.pi_gt_three
  refine measure_angleImage_eq_of_union (c := Real.pi / 2) (d := Real.pi) (by linarith)
    (I := Set.Ioc x y) (J := Set.Ioc y z)
    (fun u hu ↦ ⟨by linarith [hu.1], by linarith [hu.2]⟩)
    (fun u hu ↦ ⟨by linarith [hu.1], by linarith [hu.2]⟩)
    measurableSet_Ioc measurableSet_Ioc ?_ hI hJ S hS ?_
  · rw [Set.disjoint_left]
    intro u hu hu'
    linarith [hu.2, hu'.1]
  · rw [Set.Ioc_union_Ioc_eq_Ioc hxy hyz]
    exact hSsub

/-! ### The density identity on each full arc -/

/-- The surface measure of the angular image of any measurable subset of `[0, π/2)` is the
`rhoA`-weighted Lebesgue measure. -/
private theorem surfaceAreaMeasure_angleImage_eq_withDensity_rhoA (K : ConvexBody Point)
    (hatom0 : surfaceAreaMeasure K {((0 : ℝ) : Real.Angle)} = 0)
    (hvertexA : ∀ t ∈ Set.Ico (0 : ℝ) (Real.pi / 2),
      (edgeVertices K ((t : ℝ) : Real.Angle)).1 = paperGerverContacts t 0)
    (S : Set ℝ) (hS : MeasurableSet S) (hSsub : S ⊆ Set.Ico 0 (Real.pi / 2)) :
    surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
      volume.withDensity (fun s ↦ ENNReal.ofReal (GerverSofa.PartC.Stage2.rhoA s)) S := by
  have hpi := Real.pi_gt_three
  have hT0 : gerverStageTimes 0 = 0 := rfl
  have hlt01 : gerverStageTimes 0 < gerverStageTimes 1 := gerverStageTimes_lt_succ 0
  have hlt12 : gerverStageTimes 1 < gerverStageTimes 2 := gerverStageTimes_lt_succ 1
  have hlt23 : gerverStageTimes 2 < gerverStageTimes 3 := gerverStageTimes_lt_succ 2
  have hlt34 : gerverStageTimes 3 < gerverStageTimes 4 := gerverStageTimes_lt_succ 3
  have h4T := gerverStageTimes_four_lt_pi_div_two
  have h1T : gerverStageTimes 1 < Real.pi / 2 := by linarith
  have h2T : gerverStageTimes 2 < Real.pi / 2 := by linarith
  have h3T : gerverStageTimes 3 < Real.pi / 2 := by linarith
  have h04 : gerverStageTimes 0 ≤ gerverStageTimes 4 := by linarith
  -- the left endpoint carries no atom
  have hzeroA : ∀ S, MeasurableSet S →
      S ⊆ Set.Icc (gerverStageTimes 0) (gerverStageTimes 0) →
      surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
        volume.withDensity (fun s ↦ ENNReal.ofReal (GerverSofa.PartC.Stage2.rhoA s)) S := by
    intro S hS hSsub
    have h1 : surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S) = 0 := by
      refine measure_mono_null ?_ hatom0
      rintro u ⟨x, hx, rfl⟩
      have hx' := hSsub hx
      rw [Set.Icc_self, Set.mem_singleton_iff, hT0] at hx'
      rw [hx']
      exact rfl
    have h2 : volume.withDensity
        (fun s ↦ ENNReal.ofReal (GerverSofa.PartC.Stage2.rhoA s)) S = 0 := by
      refine measure_mono_null hSsub ?_
      rw [Set.Icc_self]
      exact (withDensity_absolutelyContinuous volume _) (measure_singleton _)
    rw [h1, h2]
  -- glue the left endpoint and the first four stages
  have hstep1 := surfaceAreaMeasure_angleImage_eq_withDensity_rhoA_of_union K
    (gerverStageTimes 0) (gerverStageTimes 0) (gerverStageTimes 1)
    hT0.ge le_rfl hlt01.le h1T.le hzeroA
    (surfaceAreaMeasure_angleImage_eq_withDensity_rhoA_of_stage K hvertexA 0 _ _
      (le_refl _) (le_refl _) h1T)
  have hstep2 := surfaceAreaMeasure_angleImage_eq_withDensity_rhoA_of_union K
    (gerverStageTimes 0) (gerverStageTimes 1) (gerverStageTimes 2)
    hT0.ge hlt01.le hlt12.le h2T.le hstep1
    (surfaceAreaMeasure_angleImage_eq_withDensity_rhoA_of_stage K hvertexA 1 _ _
      (le_refl _) (le_refl _) h2T)
  have hstep3 := surfaceAreaMeasure_angleImage_eq_withDensity_rhoA_of_union K
    (gerverStageTimes 0) (gerverStageTimes 2) (gerverStageTimes 3)
    hT0.ge (by linarith) hlt23.le h3T.le hstep2
    (surfaceAreaMeasure_angleImage_eq_withDensity_rhoA_of_stage K hvertexA 2 _ _
      (le_refl _) (le_refl _) h3T)
  have hstep4 := surfaceAreaMeasure_angleImage_eq_withDensity_rhoA_of_union K
    (gerverStageTimes 0) (gerverStageTimes 3) (gerverStageTimes 4)
    hT0.ge (by linarith) hlt34.le h4T.le hstep3
    (surfaceAreaMeasure_angleImage_eq_withDensity_rhoA_of_stage K hvertexA 3 _ _
      (le_refl _) (le_refl _) h4T)
  -- glue the exhausted last stage
  refine measure_angleImage_eq_of_union (c := -1) (d := Real.pi / 2) (by linarith)
    (I := Set.Icc (gerverStageTimes 0) (gerverStageTimes 4))
    (J := Set.Ioo (gerverStageTimes 4) (Real.pi / 2))
    (fun u hu ↦ ⟨by linarith [hu.1, hT0], by linarith [hu.2, h4T]⟩)
    (fun u hu ↦ ⟨by linarith [hu.1, hT0, h04], by linarith [hu.2]⟩)
    measurableSet_Icc measurableSet_Ioo ?_ hstep4
    (surfaceAreaMeasure_angleImage_eq_withDensity_rhoA_of_final_stage K hvertexA) S hS ?_
  · rw [Set.disjoint_left]
    intro u hu hu'
    linarith [hu.2, hu'.1]
  · rw [Set.Icc_union_Ioo_eq_Ico h04 h4T, hT0]
    exact hSsub

/-- The surface measure of the angular image of any measurable subset of `(π/2, π]` is the
translated `rhoC`-weighted Lebesgue measure. -/
private theorem surfaceAreaMeasure_angleImage_eq_withDensity_rhoC (K : ConvexBody Point)
    (hvertexC : ∀ s ∈ Set.Icc (Real.pi / 2) Real.pi,
      (edgeVertices K ((s : ℝ) : Real.Angle)).1 = paperGerverContacts (s - Real.pi / 2) 2)
    (S : Set ℝ) (hS : MeasurableSet S)
    (hSsub : S ⊆ Set.Ioc (Real.pi / 2) (Real.pi / 2 + Real.pi / 2)) :
    surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
      volume.withDensity
        (fun u ↦ ENNReal.ofReal (GerverSofa.PartC.Stage2.rhoC (u - Real.pi / 2))) S := by
  have hpi := Real.pi_gt_three
  have hT0 : gerverStageTimes 0 = 0 := rfl
  have hT5 : gerverStageTimes 5 = Real.pi / 2 := rfl
  have hlt01 : gerverStageTimes 0 < gerverStageTimes 1 := gerverStageTimes_lt_succ 0
  have hlt12 : gerverStageTimes 1 < gerverStageTimes 2 := gerverStageTimes_lt_succ 1
  have hlt23 : gerverStageTimes 2 < gerverStageTimes 3 := gerverStageTimes_lt_succ 2
  have hlt34 : gerverStageTimes 3 < gerverStageTimes 4 := gerverStageTimes_lt_succ 3
  have hlt45 : gerverStageTimes 4 < gerverStageTimes 5 := gerverStageTimes_lt_succ 4
  have hc0 := surfaceAreaMeasure_angleImage_eq_withDensity_rhoC_of_stage K hvertexC 0
    (Real.pi / 2 + gerverStageTimes 0) (Real.pi / 2 + gerverStageTimes 1) (le_refl _) (le_refl _)
  have hc1 := surfaceAreaMeasure_angleImage_eq_withDensity_rhoC_of_stage K hvertexC 1
    (Real.pi / 2 + gerverStageTimes 1) (Real.pi / 2 + gerverStageTimes 2) (le_refl _) (le_refl _)
  have hc2 := surfaceAreaMeasure_angleImage_eq_withDensity_rhoC_of_stage K hvertexC 2
    (Real.pi / 2 + gerverStageTimes 2) (Real.pi / 2 + gerverStageTimes 3) (le_refl _) (le_refl _)
  have hc3 := surfaceAreaMeasure_angleImage_eq_withDensity_rhoC_of_stage K hvertexC 3
    (Real.pi / 2 + gerverStageTimes 3) (Real.pi / 2 + gerverStageTimes 4) (le_refl _) (le_refl _)
  have hc4 := surfaceAreaMeasure_angleImage_eq_withDensity_rhoC_of_stage K hvertexC 4
    (Real.pi / 2 + gerverStageTimes 4) (Real.pi / 2 + gerverStageTimes 5) (le_refl _) (le_refl _)
  have hstep1 := surfaceAreaMeasure_angleImage_eq_withDensity_rhoC_of_union K
    (Real.pi / 2 + gerverStageTimes 0)
    (Real.pi / 2 + gerverStageTimes 1) (Real.pi / 2 + gerverStageTimes 2)
    (by linarith [gerverStageTimes_nonneg 0]) (by linarith) (by linarith)
    (by linarith [gerverStageTimes_le_pi_div_two 2]) hc0 hc1
  have hstep2 := surfaceAreaMeasure_angleImage_eq_withDensity_rhoC_of_union K
    (Real.pi / 2 + gerverStageTimes 0)
    (Real.pi / 2 + gerverStageTimes 2) (Real.pi / 2 + gerverStageTimes 3)
    (by linarith [gerverStageTimes_nonneg 0]) (by linarith) (by linarith)
    (by linarith [gerverStageTimes_le_pi_div_two 3]) hstep1 hc2
  have hstep3 := surfaceAreaMeasure_angleImage_eq_withDensity_rhoC_of_union K
    (Real.pi / 2 + gerverStageTimes 0)
    (Real.pi / 2 + gerverStageTimes 3) (Real.pi / 2 + gerverStageTimes 4)
    (by linarith [gerverStageTimes_nonneg 0]) (by linarith) (by linarith)
    (by linarith [gerverStageTimes_le_pi_div_two 4]) hstep2 hc3
  have hstep4 := surfaceAreaMeasure_angleImage_eq_withDensity_rhoC_of_union K
    (Real.pi / 2 + gerverStageTimes 0)
    (Real.pi / 2 + gerverStageTimes 4) (Real.pi / 2 + gerverStageTimes 5)
    (by linarith [gerverStageTimes_nonneg 0]) (by linarith) (by linarith)
    (by linarith [gerverStageTimes_le_pi_div_two 5]) hstep3 hc4
  refine hstep4 S hS ?_
  rw [hT0, hT5, add_zero]
  exact hSsub

theorem gerver_surface_densities :
    ∃ K : RightAngleCapSpace,
      (K.val : Set Point) = capOfSofa paperGerverSofa (Real.pi / 2) ∧
      ∃ r s : ℝ → ℝ≥0, HasCapDensities K r s ∧
        (∃ M : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
          (r t : ℝ) ≤ M ∧ (s t : ℝ) ≤ M) ∧
        (∀ i : Fin 5, ∀ t ∈ Set.Ioo (gerverStageTimes i.castSucc) (gerverStageTimes i.succ),
          HasDerivAt (fun u ↦ paperGerverContacts u 0)
            ((r t : ℝ) • tangentVector (t : Real.Angle)) t ∧
          HasDerivAt (fun u ↦ paperGerverContacts u 2)
            (-(s t : ℝ) • normalVector (t : Real.Angle)) t) := by
  obtain ⟨K, hKcap, hatom0, hvertexA, hvertexC⟩ := exists_gerverCap_positiveVertex
  obtain ⟨M, hM⟩ := exists_bound_rhoA_rhoC
  refine ⟨K, hKcap, fun t ↦ Real.toNNReal (GerverSofa.PartC.Stage2.rhoA t),
    fun t ↦ Real.toNNReal (GerverSofa.PartC.Stage2.rhoC t),
    ⟨measurable_real_toNNReal.comp measurable_rhoA,
      measurable_real_toNNReal.comp measurable_rhoC, ?_, ?_⟩,
    ⟨max M 0, fun t ht ↦ ⟨?_, ?_⟩⟩, ?_⟩
  · exact surfaceAreaMeasure_restrict_eq_map_withDensity measurableSet_Ico
      (surfaceAreaMeasure_angleImage_eq_withDensity_rhoA K.val hatom0 hvertexA)
  · rw [show Set.Ioc (Real.pi / 2) Real.pi =
      Set.Ioc (Real.pi / 2) (Real.pi / 2 + Real.pi / 2) from by
        rw [show Real.pi / 2 + Real.pi / 2 = Real.pi from by ring]]
    exact surfaceAreaMeasure_restrict_eq_map_add_withDensity
      (surfaceAreaMeasure_angleImage_eq_withDensity_rhoC K.val hvertexC)
  · rw [Real.coe_toNNReal']
    exact max_le_max (hM t ht).1 le_rfl
  · rw [Real.coe_toNNReal']
    exact max_le_max (hM t ht).2 le_rfl
  · intro i t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
      ⟨le_trans (gerverStageTimes_nonneg _) ht.1.le,
        le_trans ht.2.le (gerverStageTimes_le_pi_div_two _)⟩
    obtain ⟨hA, hC⟩ := hasDerivAt_paperGerverContacts_of_mem_stage i ht
    rw [Real.coe_toNNReal _ (GerverSofa.PartC.Stage2.rhoA_nonneg htIcc),
      Real.coe_toNNReal _ (GerverSofa.PartC.Stage2.rhoC_nonneg htIcc)]
    exact ⟨hA, hC⟩

end MovingSofa
