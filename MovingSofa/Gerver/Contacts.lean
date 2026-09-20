import MovingSofa.Gerver.DirectRegularity
import MovingSofa.Gerver.PaperPath
import MovingSofa.Gerver.ParameterIdentification

noncomputable section

open scoped ContDiff

namespace MovingSofa

def paperGerverVelocityComponents (t : ℝ) : ℝ × ℝ :=
  (inner ℝ (deriv paperGerverPath t) (normalVector (t : Real.Angle)),
    inner ℝ (deriv paperGerverPath t) (tangentVector (t : Real.Angle)))

def paperGerverContacts (t : ℝ) : Fin 4 → Point :=
  ![paperGerverPath t + (paperGerverVelocityComponents t).1 • tangentVector (t : Real.Angle) +
      normalVector (t : Real.Angle),
    paperGerverPath t + (paperGerverVelocityComponents t).1 • tangentVector (t : Real.Angle),
    paperGerverPath t - (paperGerverVelocityComponents t).2 • normalVector (t : Real.Angle) +
      tangentVector (t : Real.Angle),
    paperGerverPath t - (paperGerverVelocityComponents t).2 • normalVector (t : Real.Angle)]

def paperGerverContactData : (ℝ → ℝ × ℝ) × (ℝ → Fin 4 → Point) :=
  (paperGerverVelocityComponents, paperGerverContacts)

def gerverBranchVelocityComponents (i : Fin 5) (t : ℝ) : ℝ × ℝ :=
  ![GerverSofa.Romik.alphaBeta1 GerverSofa.PartB.params t,
    GerverSofa.Romik.alphaBeta2 GerverSofa.PartB.params t,
    GerverSofa.Romik.alphaBeta3 GerverSofa.PartB.params t,
    GerverSofa.Romik.alphaBeta4 GerverSofa.PartB.params t,
    GerverSofa.Romik.alphaBeta5 GerverSofa.PartB.params t] i

/-! ### The common shape of the four contact curves

`paperGerverContacts` is an instance of a generic four-slot shape built from a base curve
and two scalar coefficient functions.  Continuity and smoothness of the shape are proved
once here and reused for the ambient curve and for each analytic stage branch. -/

/-- The four contact curves are continuous as soon as the base curve and the two
coefficient functions are. -/
private theorem continuous_contactShape (X : ℝ → Point) (A B : ℝ → ℝ) (hX : Continuous X)
    (hA : Continuous A) (hB : Continuous B) :
    Continuous fun t : ℝ => (![
      X t + A t • tangentVector (t : Real.Angle) + normalVector (t : Real.Angle),
      X t + A t • tangentVector (t : Real.Angle),
      X t - B t • normalVector (t : Real.Angle) + tangentVector (t : Real.Angle),
      X t - B t • normalVector (t : Real.Angle)] : Fin 4 → Point) := by
  have hN : Continuous fun t : ℝ => normalVector (t : Real.Angle) :=
    contDiff_normalVector.continuous
  have hT : Continuous fun t : ℝ => tangentVector (t : Real.Angle) :=
    contDiff_tangentVector.continuous
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact (hX.add (hA.smul hT)).add hN
  · exact hX.add (hA.smul hT)
  · exact (hX.sub (hB.smul hN)).add hT
  · exact hX.sub (hB.smul hN)

/-- The four contact curves are smooth as soon as the base curve and the two coefficient
functions are. -/
private theorem contDiff_contactShape (X : ℝ → Point) (A B : ℝ → ℝ)
    (hX : ContDiff ℝ ∞ X) (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ fun t : ℝ => (![
      X t + A t • tangentVector (t : Real.Angle) + normalVector (t : Real.Angle),
      X t + A t • tangentVector (t : Real.Angle),
      X t - B t • normalVector (t : Real.Angle) + tangentVector (t : Real.Angle),
      X t - B t • normalVector (t : Real.Angle)] : Fin 4 → Point) := by
  rw [contDiff_pi]
  intro i
  fin_cases i
  · exact (hX.add (hA.smul contDiff_tangentVector)).add contDiff_normalVector
  · exact hX.add (hA.smul contDiff_tangentVector)
  · exact (hX.sub (hB.smul contDiff_normalVector)).add contDiff_tangentVector
  · exact hX.sub (hB.smul contDiff_normalVector)

open GerverSofa.Romik GerverSofa.PartF.Coordinates in
theorem paperGerverContactData_properties :
    Continuous paperGerverVelocityComponents ∧ Continuous paperGerverContacts ∧
    (∀ i : Fin 5, ContDiffOn ℝ ∞ paperGerverContacts (gerverStageIntervals i)) ∧
    (∀ i : Fin 5, ∀ t ∈ gerverStageIntervals i,
      paperGerverVelocityComponents t = gerverBranchVelocityComponents i t) := by
  -- Abbreviate the certified direct parameter vector, and order its switching angles.
  obtain ⟨p, hp⟩ : ∃ p : Params, GerverSofa.PartB.params = p := ⟨_, rfl⟩
  have hmem : p ∈ gerverDirectBox := hp ▸ GerverSofa.PartB.params_mem
  have heqs : gerverDirectEquations p := hp ▸ GerverSofa.PartB.params_equations
  obtain ⟨hC1, -, -⟩ := gerver_direct_path_regularity p hmem heqs
  obtain ⟨-, hphi, htheta, hphipos, hphitheta, hthetalt, -⟩ :=
    gerver_parameter_identification.1 p hmem heqs
  have hphi' : p.phi = GerversSofa.φ := hphi.trans selected_phi
  have htheta' : p.theta = GerversSofa.θ := htheta.trans selected_theta
  have h0 : (0 : ℝ) < p.phi := by rw [hphi]; exact hphipos
  have h1 : p.phi < p.theta := by rw [hphi, htheta]; exact hphitheta
  have h2 : p.theta < Real.pi / 4 := by rw [htheta]; exact hthetalt
  have hC1' : ContDiff ℝ 1 (path GerverSofa.PartB.params) := by rw [hp]; exact hC1
  -- The velocity components read off the body-frame derivative of the direct path.
  have hvel : ∀ (w : GerverSofa.Point) (t : ℝ), deriv (path p) t = rot t w →
      paperGerverVelocityComponents t = w := by
    intro w t hw
    have hd : deriv paperGerverPath t = toPlane (rot t w) := by
      rw [deriv_paperGerverPath hC1' t, hp, hw]
    simp only [paperGerverVelocityComponents, hd, inner_toPlane_rot_normalVector,
      inner_toPlane_rot_tangentVector]
  have hvelC : Continuous paperGerverVelocityComponents :=
    ((continuous_deriv_paperGerverPath hC1').inner contDiff_normalVector.continuous).prodMk
      ((continuous_deriv_paperGerverPath hC1').inner contDiff_tangentVector.continuous)
  -- Stage smoothness: the contacts agree there with the smooth analytic branch data.
  have hstage : ∀ (X W : ℝ → GerverSofa.Point) (s : Set ℝ), ContDiff ℝ ∞ X →
      ContDiff ℝ ∞ W → (∀ t ∈ s, path p t = X t) →
      (∀ t ∈ s, deriv (path p) t = rot t (W t)) →
      ContDiffOn ℝ ∞ paperGerverContacts s := by
    intro X W s hX hW hXe hWe
    refine (contDiff_contactShape (fun t => toPlane (X t)) (fun t => (W t).1)
      (fun t => (W t).2) (contDiff_toPlane hX) hW.fst hW.snd).contDiffOn.congr ?_
    intro t ht
    have hx : paperGerverPath t = toPlane (X t) := by
      show toPlane (path GerverSofa.PartB.params t) = toPlane (X t)
      rw [hp]
      exact congrArg toPlane (hXe t ht)
    simp only [paperGerverContacts, hx, hvel (W t) t (hWe t ht)]
  -- The five stage intervals, in terms of the direct switching angles.
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
  -- The stage coefficient pairs, read off the vector of branch velocities.
  have hB0 : ∀ t, gerverBranchVelocityComponents 0 t = alphaBeta1 p t := fun t => by
    simp [gerverBranchVelocityComponents, hp]
  have hB1 : ∀ t, gerverBranchVelocityComponents 1 t = alphaBeta2 p t := fun t => by
    simp [gerverBranchVelocityComponents, hp]
  have hB2 : ∀ t, gerverBranchVelocityComponents 2 t = alphaBeta3 p t := fun t => by
    simp [gerverBranchVelocityComponents, hp]
  have hB3 : ∀ t, gerverBranchVelocityComponents 3 t = alphaBeta4 p t := fun t => by
    simp [gerverBranchVelocityComponents, hp]
  have hB4 : ∀ t, gerverBranchVelocityComponents 4 t = alphaBeta5 p t := fun t => by
    simp [gerverBranchVelocityComponents, hp]
  refine ⟨hvelC, ?_, ?_, ?_⟩
  · exact continuous_contactShape paperGerverPath
      (fun t => (paperGerverVelocityComponents t).1)
      (fun t => (paperGerverVelocityComponents t).2) (continuous_paperGerverPath hC1')
      hvelC.fst hvelC.snd
  · intro i
    fin_cases i
    · exact hstage (path1 p) (alphaBeta1 p) (gerverStageIntervals 0) (contDiff_path1 p)
        (contDiff_alphaBeta1 p) (fun t ht => path_eq_path1_of_mem_Icc p (hI0 ▸ ht))
        (fun t ht => deriv_path_eq_rot_alphaBeta1 hC1 h0 (hI0 ▸ ht))
    · exact hstage (path2 p) (alphaBeta2 p) (gerverStageIntervals 1) (contDiff_path2 p)
        (contDiff_alphaBeta2 p) (fun t ht => path_eq_path2_of_mem_Icc heqs (hI1 ▸ ht))
        (fun t ht => deriv_path_eq_rot_alphaBeta2 hC1 heqs h1 (hI1 ▸ ht))
    · exact hstage (path3 p) (alphaBeta3 p) (gerverStageIntervals 2) (contDiff_path3 p)
        (contDiff_alphaBeta3 p) (fun t ht => path_eq_path3_of_mem_Icc heqs h1 (hI2 ▸ ht))
        (fun t ht => deriv_path_eq_rot_alphaBeta3 hC1 heqs h1 h2 (hI2 ▸ ht))
    · exact hstage (path4 p) (alphaBeta4 p) (gerverStageIntervals 3) (contDiff_path4 p)
        (contDiff_alphaBeta4 p) (fun t ht => path_eq_path4_of_mem_Icc heqs h1 h2 (hI3 ▸ ht))
        (fun t ht => deriv_path_eq_rot_alphaBeta4 hC1 heqs h1 h2 (hI3 ▸ ht))
    · exact hstage (path5 p) (alphaBeta5 p) (gerverStageIntervals 4) (contDiff_path5 p)
        (contDiff_alphaBeta5 p) (fun t ht => path_eq_path5_of_mem_Icc heqs h1 h2 (hI4 ▸ ht))
        (fun t ht => deriv_path_eq_rot_alphaBeta5 hC1 heqs h0 h1 h2 (hI4 ▸ ht))
  · intro i
    fin_cases i
    · exact fun t ht => (hvel _ t (deriv_path_eq_rot_alphaBeta1 hC1 h0
        (hI0 ▸ (ht : t ∈ gerverStageIntervals 0)))).trans (hB0 t).symm
    · exact fun t ht => (hvel _ t (deriv_path_eq_rot_alphaBeta2 hC1 heqs h1
        (hI1 ▸ (ht : t ∈ gerverStageIntervals 1)))).trans (hB1 t).symm
    · exact fun t ht => (hvel _ t (deriv_path_eq_rot_alphaBeta3 hC1 heqs h1 h2
        (hI2 ▸ (ht : t ∈ gerverStageIntervals 2)))).trans (hB2 t).symm
    · exact fun t ht => (hvel _ t (deriv_path_eq_rot_alphaBeta4 hC1 heqs h1 h2
        (hI3 ▸ (ht : t ∈ gerverStageIntervals 3)))).trans (hB3 t).symm
    · exact fun t ht => (hvel _ t (deriv_path_eq_rot_alphaBeta5 hC1 heqs h0 h1 h2
        (hI4 ▸ (ht : t ∈ gerverStageIntervals 4)))).trans (hB4 t).symm

/-! ### Identification with the certified piecewise contact data -/

/-- On the physical rotation interval the paper velocity components agree with the vendor
piecewise body-frame coefficients. -/
theorem paperGerverVelocityComponents_eq_alphaBetaAt (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    paperGerverVelocityComponents t = GerverSofa.PartC.alphaBetaAt t := by
  obtain ⟨-, hphi, htheta, -⟩ := gerver_parameter_identification.1 GerverSofa.PartB.params
    GerverSofa.PartB.params_mem GerverSofa.PartB.params_equations
  have hphi' : GerverSofa.PartB.params.phi = GerversSofa.φ := hphi.trans selected_phi
  have htheta' : GerverSofa.PartB.params.theta = GerversSofa.θ := htheta.trans selected_theta
  have hvel := paperGerverContactData_properties.2.2.2
  have hI0 : gerverStageIntervals 0 = Set.Icc 0 GerversSofa.φ := by
    simp [gerverStageIntervals, gerverStageTimes]
  have hI1 : gerverStageIntervals 1 = Set.Icc GerversSofa.φ GerversSofa.θ := by
    simp [gerverStageIntervals, gerverStageTimes]
  have hI2 : gerverStageIntervals 2 = Set.Icc GerversSofa.θ (Real.pi / 2 - GerversSofa.θ) := by
    simp [gerverStageIntervals, gerverStageTimes]
  have hI3 : gerverStageIntervals 3 =
      Set.Icc (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2 - GerversSofa.φ) := by
    simp [gerverStageIntervals, gerverStageTimes]
  have hI4 : gerverStageIntervals 4 = Set.Icc (Real.pi / 2 - GerversSofa.φ) (Real.pi / 2) := by
    simp [gerverStageIntervals, gerverStageTimes]
  obtain ⟨ht0, ht2⟩ := ht
  simp only [GerverSofa.PartC.alphaBetaAt, GerverSofa.PartC.eta, GerverSofa.PartC.tau,
    GerverSofa.PartC.T, hphi', htheta']
  split_ifs with h1 h2 h3 h4
  · have := hvel 0 t (by rw [hI0]; exact ⟨ht0, h1⟩)
    simpa [gerverBranchVelocityComponents] using this
  · have := hvel 1 t (by rw [hI1]; exact ⟨le_of_not_ge h1, h2⟩)
    simpa [gerverBranchVelocityComponents] using this
  · have := hvel 2 t (by rw [hI2]; exact ⟨le_of_not_ge h2, h3⟩)
    simpa [gerverBranchVelocityComponents] using this
  · have := hvel 3 t (by rw [hI3]; exact ⟨le_of_not_ge h3, h4⟩)
    simpa [gerverBranchVelocityComponents] using this
  · have := hvel 4 t (by rw [hI4]; exact ⟨le_of_not_ge h4, ht2⟩)
    simpa [gerverBranchVelocityComponents] using this

/-- On the physical rotation interval the four paper contact curves are the coordinate
transports of the four certified contact curves. -/
theorem fromPlane_paperGerverContacts (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2))
    (i : Fin 4) :
    GerverSofa.PartF.Coordinates.fromPlane (paperGerverContacts t i) =
      ![GerverSofa.PartC.A t, GerverSofa.PartC.B t, GerverSofa.PartC.C t,
        GerverSofa.PartC.D t] i := by
  have hab := paperGerverVelocityComponents_eq_alphaBetaAt t ht
  fin_cases i <;> simp only [paperGerverContacts, hab] <;> rfl

/-- On the physical rotation interval the second paper contact curve is the certified curve
`B`, read in plane coordinates. -/
theorem paperGerverContacts_one_eq_toPlane {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    paperGerverContacts t 1 =
      GerverSofa.PartF.Coordinates.toPlane (GerverSofa.PartC.B t) :=
  (GerverSofa.PartF.Coordinates.toPlane_fromPlane _).symm.trans
    (congrArg GerverSofa.PartF.Coordinates.toPlane (fromPlane_paperGerverContacts t ht 1))

/-- On the physical rotation interval the fourth paper contact curve is the certified curve
`D`, read in plane coordinates. -/
theorem paperGerverContacts_three_eq_toPlane {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    paperGerverContacts t 3 =
      GerverSofa.PartF.Coordinates.toPlane (GerverSofa.PartC.D t) :=
  (GerverSofa.PartF.Coordinates.toPlane_fromPlane _).symm.trans
    (congrArg GerverSofa.PartF.Coordinates.toPlane (fromPlane_paperGerverContacts t ht 3))

end MovingSofa
