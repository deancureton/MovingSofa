import MovingSofa.Canonical.GerverDefinitions

noncomputable section

namespace MovingSofa

/-- The two Gerver switching angles and the right/left distinguished angles. -/
def paperGerverConstants : (ℝ × ℝ) × (ℝ × ℝ) :=
  ((GerversSofa.φ, GerversSofa.θ), (GerversSofa.φ, Real.pi / 2 - GerversSofa.φ))

/-- The six endpoints of the five Gerver stages. -/
def gerverStageTimes : Fin 6 → ℝ :=
  ![0, GerversSofa.φ, GerversSofa.θ, Real.pi / 2 - GerversSofa.θ,
    Real.pi / 2 - GerversSofa.φ, Real.pi / 2]

/-- The five closed stage intervals in their source order. -/
def gerverStageIntervals (i : Fin 5) : Set ℝ :=
  Set.Icc (gerverStageTimes i.castSucc) (gerverStageTimes i.succ)

/-- The exact direct 22-equation Gerver system, with the certified phase-map convention. -/
def gerverDirectEquations (p : GerverSofa.Romik.Params) : Prop :=
  GerverSofa.Romik.Equations p

/-- The exact closed rational box for the direct Gerver parameters. -/
def gerverDirectBox : Set GerverSofa.Romik.Params := GerverSofa.Romik.box

/-- The exact box bounds the second-stage linear coefficient `b₁` from below by `-53/100`. -/
theorem gerverDirectBox_b1_lower_bound {p : GerverSofa.Romik.Params} (hp : p ∈ gerverDirectBox) :
    (-53 : ℝ) / 100 ≤ p.b1 := by
  dsimp only [gerverDirectBox, GerverSofa.Romik.box, GerverSofa.qR, Set.mem_ofPred_eq] at hp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, -, hb1, -⟩ := hp
  exact le_trans (by norm_num) hb1

/-- The exact box bounds the fourth-stage linear coefficient `d₁` from above by `33/25`. -/
theorem gerverDirectBox_d1_upper_bound {p : GerverSofa.Romik.Params} (hp : p ∈ gerverDirectBox) :
    p.d1 ≤ (33 : ℝ) / 25 := by
  dsimp only [gerverDirectBox, GerverSofa.Romik.box, GerverSofa.qR, Set.mem_ofPred_eq] at hp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, -, -, -, -, -, -, -, -, -, -, hd1, -⟩ := hp
  exact le_trans hd1 (by norm_num)

end MovingSofa
