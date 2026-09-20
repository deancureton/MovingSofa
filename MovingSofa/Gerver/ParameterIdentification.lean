import MovingSofa.Gerver.ReversePhysicalDomain

noncomputable section

namespace MovingSofa

open GerverSofa.PartF.ProjectAdapter (selected)

/-- The adapter's selected reverse parameter vector carries the paper's angle `φ` in its
`phi` field.  This is true by definition — `selected` is built from the very quadruple that
defines `GerversSofa.φ` — but it is the only bridge from the vendor parameter vector to the
paper's stage times `gerverStageTimes`, so it is recorded as a named lemma rather than left
to an invisible unfolding at each use site. -/
theorem selected_phi : selected.phi = GerversSofa.φ := rfl

/-- The adapter's selected reverse parameter vector carries the paper's angle `θ` in its
`theta` field; see `selected_phi` for why this `rfl` is worth naming. -/
theorem selected_theta : selected.theta = GerversSofa.θ := rfl

theorem gerver_parameter_identification :
    (∀ p : GerverSofa.Romik.Params, p ∈ gerverDirectBox → gerverDirectEquations p →
      p = gerverParameterDictionary.1 selected ∧
      p.phi = selected.phi ∧ p.theta = selected.theta ∧
      0 < selected.phi ∧ selected.phi < selected.theta ∧ selected.theta < Real.pi / 4 ∧
      (39 : ℝ) / 1000 ≤ selected.phi ∧ selected.phi ≤ (40 : ℝ) / 1000 ∧
      GerversSofa.ABφθSpec selected.a selected.b selected.phi selected.theta) ∧
    (∃ p : GerverSofa.Romik.Params, p ∈ gerverDirectBox ∧ gerverDirectEquations p ∧
      p = gerverParameterDictionary.1 selected) := by
  -- The reverse parameters of any direct solution in the box satisfy the whole
  -- reduced specification, whose unique solution is the selected quadruple.
  have key : ∀ p : GerverSofa.Romik.Params, p ∈ gerverDirectBox → gerverDirectEquations p →
      gerverParameterDictionary.2 p = selected := by
    intro p hp heq
    rw [GerverSofa.PartF.ProjectAdapter.selected_eq_certified]
    exact GerverSofa.PartF.Parameters.undictionary_eq_reduced_certified hp heq
  -- Reconstruction then recovers the direct vector from its reverse parameters.
  have hdict : ∀ p : GerverSofa.Romik.Params, p ∈ gerverDirectBox → gerverDirectEquations p →
      p = gerverParameterDictionary.1 selected := by
    intro p hp heq
    calc p = GerverSofa.PartF.Phases.dictionary (gerverParameterDictionary.2 p) :=
          (GerverSofa.PartF.Phases.dictionary_undictionary_of_equations heq).symm
      _ = gerverParameterDictionary.1 selected :=
          congrArg GerverSofa.PartF.Phases.dictionary (key p hp heq)
  have hspec : GerversSofa.ABφθSpec selected.a selected.b selected.phi selected.theta :=
    GerversSofa.ABφθSpec.existsUnique.choose_spec.1
  refine ⟨fun p hp heq => ?_, GerverSofa.PartB.params, GerverSofa.PartB.params_mem,
    GerverSofa.PartB.params_equations,
    hdict _ GerverSofa.PartB.params_mem GerverSofa.PartB.params_equations⟩
  obtain ⟨hphipos, hphitheta, htheta, -, -, hphilo, hphihi⟩ :=
    gerver_reverse_physical_domain p hp
  have hu := key p hp heq
  rw [hu] at hphipos hphitheta htheta hphilo hphihi
  exact ⟨hdict p hp heq, congrArg GerverSofa.Reduced.Params.phi hu,
    congrArg GerverSofa.Reduced.Params.theta hu, hphipos, hphitheta, htheta, hphilo, hphihi,
    hspec⟩

/-- The two distinguished Gerver angles are interior and complementary. -/
theorem paperGerverConstants_snd_mem_Ioo :
    paperGerverConstants.2.1 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) ∧
      paperGerverConstants.2.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) ∧
      paperGerverConstants.2.1 + paperGerverConstants.2.2 = Real.pi / 2 := by
  have hpos : 0 < GerversSofa.φ := by
    obtain ⟨hall, q, hqbox, hqeq, -⟩ := gerver_parameter_identification
    exact (hall q hqbox hqeq).2.2.2.1
  have hle : GerversSofa.φ ≤ Real.pi / 4 := by
    have h := GerversSofa.ABφθSpec.existsUnique.choose_spec.1
    exact le_trans h.2.1 h.2.2.1
  have hpi := Real.pi_pos
  have h1 : paperGerverConstants.2.1 = GerversSofa.φ := rfl
  have h2 : paperGerverConstants.2.2 = Real.pi / 2 - GerversSofa.φ := rfl
  rw [h1, h2]
  refine ⟨⟨hpos, by linarith only [hle, hpi]⟩,
    ⟨by linarith only [hle, hpi], by linarith only [hpos]⟩, by ring⟩

/-- The two distinguished angles are ordered: the certified bound `φ ≤ 1/25` puts `φ` well below
`π/4 = π/2 - π/4`. -/
theorem paperGerverConstants_snd_fst_lt_snd_snd :
    paperGerverConstants.2.1 < paperGerverConstants.2.2 := by
  obtain ⟨-, -, hsum⟩ := paperGerverConstants_snd_mem_Ioo
  have hphi : paperGerverConstants.2.1 ≤ (40 : ℝ) / 1000 := by
    obtain ⟨hall, p, hpbox, hpeq, -⟩ := gerver_parameter_identification
    exact (hall p hpbox hpeq).2.2.2.2.2.2.2.1
  have := Real.pi_gt_three
  linarith

/-! ### The stage times as certified angles

`gerverStageTimes` is defined from the paper angles `GerversSofa.φ` and `GerversSofa.θ`,
while the certified Part C geometry is indexed by the vendor parameter fields
`params.phi`, `params.theta` and the derived angles `eta`, `tau`, `T`.  The six lemmas
below are the dictionary between the two indexings; they are the only place where
`gerver_parameter_identification` is needed to see a stage time. -/

/-- The zeroth stage time is the start of the rotation interval. -/
theorem gerverStageTimes_zero : gerverStageTimes 0 = 0 := rfl

/-- The first stage time is the certified first switching angle `params.phi`. -/
theorem gerverStageTimes_one : gerverStageTimes 1 = GerverSofa.PartC.params.phi := by
  obtain ⟨-, hphi, -⟩ := gerver_parameter_identification.1 GerverSofa.PartB.params
    GerverSofa.PartB.params_mem GerverSofa.PartB.params_equations
  simp [gerverStageTimes, hphi.trans selected_phi]

/-- The second stage time is the certified second switching angle `params.theta`. -/
theorem gerverStageTimes_two : gerverStageTimes 2 = GerverSofa.PartC.params.theta := by
  obtain ⟨-, -, htheta, -⟩ := gerver_parameter_identification.1 GerverSofa.PartB.params
    GerverSofa.PartB.params_mem GerverSofa.PartB.params_equations
  simp [gerverStageTimes, htheta.trans selected_theta]

/-- The third stage time is the certified reflected angle `eta = T - params.theta`. -/
theorem gerverStageTimes_three : gerverStageTimes 3 = GerverSofa.PartC.eta := by
  have h := gerverStageTimes_two
  simp only [gerverStageTimes, Matrix.cons_val] at h ⊢
  rw [GerverSofa.PartC.eta, GerverSofa.PartC.T, ← h]

/-- The fourth stage time is the certified reflected angle `tau = T - params.phi`. -/
theorem gerverStageTimes_four : gerverStageTimes 4 = GerverSofa.PartC.tau := by
  have h := gerverStageTimes_one
  simp only [gerverStageTimes, Matrix.cons_val] at h ⊢
  rw [GerverSofa.PartC.tau, GerverSofa.PartC.T, ← h]

/-- The fifth stage time is the certified end `T` of the rotation interval. -/
theorem gerverStageTimes_five : gerverStageTimes 5 = GerverSofa.PartC.T := rfl

end MovingSofa
