import GerverSofa.KernelOnly.PartE.DeepMindABPhiThetaBridge

/-!
# Part E02: exact reduction of the DeepMind system to two angles

E01 identified the sole missing mathematical input as a global enclosure of
all physical solutions of the four-variable reduced system.  E02 eliminates
the two linear variables `A` and `B` exactly.

The third and fourth Gerver equations first give `B` as an affine expression
in `A`, and then give `A` as a quotient depending only on `(phi, theta)`.  The
denominator is proved nonzero for every physical solution; this is a theorem,
not an additional assumption.  Consequently existence of a physical
four-variable solution is equivalent to a two-angle specification.

The remaining enclosure target quantifies only over
`0 <= phi <= theta <= pi/4`.  It is still an ordinary theorem argument: E02
does not declare the interval branch-and-bound conclusion as an axiom.
-/

noncomputable section

namespace GerverSofa
namespace PartE

/-- Difference of the two switching angles. -/
def angleDelta (phi theta : ℝ) : ℝ := theta - phi

/-- Constant part of the fourth equation after solving it for `B`. -/
def bBase (phi theta : ℝ) : ℝ :=
  Real.pi / 2 - phi - theta + angleDelta phi theta / 2 +
    angleDelta phi theta ^ 2 / 4

/-- The value of `B` forced by the fourth equation once `A` is fixed. -/
def bFromA (A phi theta : ℝ) : ℝ :=
  A * (1 + angleDelta phi theta / 2) + bBase phi theta

/-- Denominator obtained from the third equation after eliminating `B`. -/
def angleDenominator (phi theta : ℝ) : ℝ :=
  Real.cos phi - (1 + angleDelta phi theta / 2) * Real.sin phi

/-- Numerator obtained from the third equation after eliminating `B`. -/
def angleNumerator (phi theta : ℝ) : ℝ :=
  Real.sin phi + 1 / 2 - Real.cos phi / 2 +
    bBase phi theta * Real.sin phi

/-- Reconstructed value of `A`, depending only on the two angles. -/
def reconstructedA (phi theta : ℝ) : ℝ :=
  angleNumerator phi theta / angleDenominator phi theta

/-- Reconstructed value of `B`, depending only on the two angles. -/
def reconstructedB (phi theta : ℝ) : ℝ :=
  bFromA (reconstructedA phi theta) phi theta

/-- The triangular physical domain for the two switching angles. -/
def PhysicalAngleDomain (phi theta : ℝ) : Prop :=
  0 ≤ phi ∧ phi ≤ theta ∧ theta ≤ Real.pi / 4

/-- The last two displayed equations of the DeepMind system. -/
def ThirdFourthEquations (A B phi theta : ℝ) : Prop :=
  A * Real.cos phi
      - (Real.sin phi + 1 / 2 - Real.cos phi / 2 + B * Real.sin phi) = 0 ∧
  (A + Real.pi / 2 - phi - theta)
      - (B - (theta - phi) * (1 + A) / 2 - (theta - phi) ^ 2 / 4) = 0

/-- The fourth equation is exactly the affine reconstruction formula for `B`. -/
theorem fourthEquation_iff_b_eq_bFromA (A B phi theta : ℝ) :
    (A + Real.pi / 2 - phi - theta)
          - (B - (theta - phi) * (1 + A) / 2 -
            (theta - phi) ^ 2 / 4) = 0 ↔
      B = bFromA A phi theta := by
  constructor <;> intro h <;>
    dsimp [bFromA, bBase, angleDelta] at h ⊢ <;>
    ring_nf at h ⊢ <;>
    linarith

/-- After the fourth equation has reconstructed `B`, the third equation is
exactly `A * denominator = numerator`. -/
theorem thirdEquation_iff_mul_denominator_eq_numerator
    (A B phi theta : ℝ) (hB : B = bFromA A phi theta) :
    A * Real.cos phi
          - (Real.sin phi + 1 / 2 - Real.cos phi / 2 +
            B * Real.sin phi) = 0 ↔
      A * angleDenominator phi theta = angleNumerator phi theta := by
  subst B
  constructor <;> intro h <;>
    dsimp [bFromA, bBase, angleDelta, angleDenominator,
      angleNumerator] at h ⊢ <;>
    ring_nf at h ⊢ <;>
    linarith

/-- Exact simultaneous elimination statement for equations three and four. -/
theorem thirdFourthEquations_iff_eliminated (A B phi theta : ℝ) :
    ThirdFourthEquations A B phi theta ↔
      B = bFromA A phi theta ∧
        A * angleDenominator phi theta = angleNumerator phi theta := by
  constructor
  · rintro ⟨h3, h4⟩
    have hB := (fourthEquation_iff_b_eq_bFromA A B phi theta).1 h4
    exact ⟨hB,
      (thirdEquation_iff_mul_denominator_eq_numerator
        A B phi theta hB).1 h3⟩
  · rintro ⟨hB, hA⟩
    exact ⟨
      (thirdEquation_iff_mul_denominator_eq_numerator
        A B phi theta hB).2 hA,
      (fourthEquation_iff_b_eq_bFromA A B phi theta).2 hB⟩

/-- The physical four-variable domain projects to the triangular angle domain. -/
theorem physicalAngleDomain_of_physicalDomain {A B phi theta : ℝ}
    (h : PhysicalDomain (reducedParams A B phi theta)) :
    PhysicalAngleDomain phi theta := by
  exact ⟨h.1, h.2.1, h.2.2.1⟩

/-- The constant part of the reconstructed `B` is nonnegative throughout the
physical angle triangle. -/
theorem bBase_nonneg_of_physicalAngleDomain {phi theta : ℝ}
    (h : PhysicalAngleDomain phi theta) : 0 ≤ bBase phi theta := by
  rcases h with ⟨hphi0, hphiTheta, htheta⟩
  have hdelta : 0 ≤ theta - phi := sub_nonneg.mpr hphiTheta
  have hsum : phi + theta ≤ Real.pi / 2 := by
    nlinarith
  have hsquare : 0 ≤ (theta - phi) ^ 2 := sq_nonneg (theta - phi)
  dsimp [bBase, angleDelta]
  nlinarith

/-- The sine of the first switching angle is nonnegative in the physical
triangle. -/
theorem sin_phi_nonneg_of_physicalAngleDomain {phi theta : ℝ}
    (h : PhysicalAngleDomain phi theta) : 0 ≤ Real.sin phi := by
  rcases h with ⟨hphi0, hphiTheta, htheta⟩
  apply Real.sin_nonneg_of_nonneg_of_le_pi hphi0
  nlinarith [Real.pi_gt_three]

/-- The cosine of the first switching angle is strictly positive in the
physical triangle. -/
theorem cos_phi_pos_of_physicalAngleDomain {phi theta : ℝ}
    (h : PhysicalAngleDomain phi theta) : 0 < Real.cos phi := by
  rcases h with ⟨hphi0, hphiTheta, htheta⟩
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> nlinarith [Real.pi_pos]

/-- No physical solution of all four equations can hit the apparent zero
denominator of the two-angle reconstruction. -/
theorem angleDenominator_ne_zero_of_physical_and_equations
    {A B phi theta : ℝ}
    (hdom : PhysicalDomain (reducedParams A B phi theta))
    (heq : DeepMindEquations A B phi theta) :
    angleDenominator phi theta ≠ 0 := by
  have hang : PhysicalAngleDomain phi theta :=
    physicalAngleDomain_of_physicalDomain hdom
  have helim :
      B = bFromA A phi theta ∧
        A * angleDenominator phi theta = angleNumerator phi theta :=
    (thirdFourthEquations_iff_eliminated A B phi theta).1
      ⟨heq.2.2.1, heq.2.2.2⟩
  intro hden
  have hnumZero : angleNumerator phi theta = 0 := by
    rw [← helim.2, hden, mul_zero]
  have hsinNonneg : 0 ≤ Real.sin phi :=
    sin_phi_nonneg_of_physicalAngleDomain hang
  have hcosPos : 0 < Real.cos phi :=
    cos_phi_pos_of_physicalAngleDomain hang
  have hsinNe : Real.sin phi ≠ 0 := by
    intro hsin
    have hcosZero : Real.cos phi = 0 := by
      dsimp [angleDenominator, angleDelta] at hden
      rw [hsin, mul_zero, sub_zero] at hden
      exact hden
    exact (ne_of_gt hcosPos) hcosZero
  have hsinPos : 0 < Real.sin phi :=
    lt_of_le_of_ne hsinNonneg hsinNe.symm
  have hbaseNonneg : 0 ≤ bBase phi theta :=
    bBase_nonneg_of_physicalAngleDomain hang
  have hcosGap : 0 ≤ 1 / 2 - Real.cos phi / 2 := by
    nlinarith [Real.cos_le_one phi]
  have hbaseSin : 0 ≤ bBase phi theta * Real.sin phi :=
    mul_nonneg hbaseNonneg hsinNonneg
  have hnumPos : 0 < angleNumerator phi theta := by
    dsimp [angleNumerator]
    nlinarith
  exact (ne_of_gt hnumPos) hnumZero

/-- Every physical four-variable solution has the reconstructed value of `A`. -/
theorem a_eq_reconstructed_of_physical_and_equations
    {A B phi theta : ℝ}
    (hdom : PhysicalDomain (reducedParams A B phi theta))
    (heq : DeepMindEquations A B phi theta) :
    A = reconstructedA phi theta := by
  have hden :=
    angleDenominator_ne_zero_of_physical_and_equations hdom heq
  have helim :=
    (thirdFourthEquations_iff_eliminated A B phi theta).1
      ⟨heq.2.2.1, heq.2.2.2⟩
  exact (eq_div_iff hden).2 helim.2

/-- Every physical four-variable solution has the reconstructed value of `B`. -/
theorem b_eq_reconstructed_of_physical_and_equations
    {A B phi theta : ℝ}
    (hdom : PhysicalDomain (reducedParams A B phi theta))
    (heq : DeepMindEquations A B phi theta) :
    B = reconstructedB phi theta := by
  have hA := a_eq_reconstructed_of_physical_and_equations hdom heq
  have hB :=
    ((thirdFourthEquations_iff_eliminated A B phi theta).1
      ⟨heq.2.2.1, heq.2.2.2⟩).1
  calc
    B = bFromA A phi theta := hB
    _ = bFromA (reconstructedA phi theta) phi theta := by rw [hA]
    _ = reconstructedB phi theta := rfl

/-- The first two equations after exact reconstruction of `A` and `B`. -/
def TwoAngleEquations (phi theta : ℝ) : Prop :=
  let A := reconstructedA phi theta
  let B := reconstructedB phi theta
  A * (Real.cos theta - Real.cos phi) - 2 * B * Real.sin phi
      + (theta - phi - 1) * Real.cos theta - Real.sin theta
      + Real.cos phi + Real.sin phi = 0 ∧
  A * (3 * Real.sin theta + Real.sin phi) - 2 * B * Real.cos phi
      + 3 * (theta - phi - 1) * Real.sin theta + 3 * Real.cos theta
      - Real.sin phi + Real.cos phi = 0

/-- Complete two-dimensional specification equivalent to existence of a
physical solution with the given two angles. -/
def TwoAngleSpec (phi theta : ℝ) : Prop :=
  PhysicalAngleDomain phi theta ∧
    angleDenominator phi theta ≠ 0 ∧
    0 ≤ reconstructedA phi theta ∧
    0 ≤ reconstructedB phi theta ∧
    TwoAngleEquations phi theta

/-- The reconstructed parameters assembled as a reduced-system record. -/
def reconstructedParams (phi theta : ℝ) : Reduced.Params :=
  reducedParams (reconstructedA phi theta) (reconstructedB phi theta) phi theta

/-- Two-angle data reconstruct a physical solution of all four displayed
DeepMind equations. -/
theorem deepMindSpec_of_twoAngleSpec {phi theta : ℝ}
    (h : TwoAngleSpec phi theta) :
    DeepMindABPhiThetaSpec
      (reconstructedA phi theta) (reconstructedB phi theta) phi theta := by
  rcases h with ⟨hang, hden, hA0, hB0, h12⟩
  have h34 : ThirdFourthEquations
      (reconstructedA phi theta) (reconstructedB phi theta) phi theta := by
    apply (thirdFourthEquations_iff_eliminated
      (reconstructedA phi theta) (reconstructedB phi theta) phi theta).2
    constructor
    · rfl
    · simp [reconstructedA, hden]
  refine ⟨?_, ?_⟩
  · exact ⟨hang.1, hang.2.1, hang.2.2, hA0, hB0⟩
  · rcases h12 with ⟨h1, h2⟩
    exact ⟨h1, h2, h34.1, h34.2⟩

/-- Exact dimension reduction: for fixed angles, a physical four-variable
solution exists if and only if the reconstructed two-angle specification
holds. -/
theorem exists_deepMindSpec_iff_twoAngleSpec (phi theta : ℝ) :
    (∃ A B : ℝ, DeepMindABPhiThetaSpec A B phi theta) ↔
      TwoAngleSpec phi theta := by
  constructor
  · rintro ⟨A, B, hspec⟩
    have hden := angleDenominator_ne_zero_of_physical_and_equations
      hspec.1 hspec.2
    have hA := a_eq_reconstructed_of_physical_and_equations hspec.1 hspec.2
    have hB := b_eq_reconstructed_of_physical_and_equations hspec.1 hspec.2
    refine ⟨physicalAngleDomain_of_physicalDomain hspec.1, hden, ?_, ?_, ?_⟩
    · have hA0 : 0 ≤ A := by
        simpa only [reducedParams] using hspec.1.2.2.2.1
      rw [hA] at hA0
      exact hA0
    · have hB0 : 0 ≤ B := by
        simpa only [reducedParams] using hspec.1.2.2.2.2
      rw [hB] at hB0
      exact hB0
    · rcases hspec.2 with ⟨h1, h2, _h3, _h4⟩
      simpa [TwoAngleEquations, hA, hB] using And.intro h1 h2
  · intro h
    exact ⟨reconstructedA phi theta, reconstructedB phi theta,
      deepMindSpec_of_twoAngleSpec h⟩

/-- The sole mathematical target left after E02.  Unlike E01's four-variable
target, this quantifies only over the compact triangle of the two angles. -/
def TwoAngleEnclosureTarget : Prop :=
  ∀ phi theta : ℝ,
    TwoAngleSpec phi theta → reconstructedParams phi theta ∈ Reduced.box

/-- A proof of the two-angle enclosure target yields E01's full global
enclosure target. -/
theorem globalEnclosureTarget_of_twoAngleEnclosure
    (hangle : TwoAngleEnclosureTarget) : GlobalEnclosureTarget := by
  intro p hdom heq
  have hdeep : DeepMindEquations p.a p.b p.phi p.theta :=
    (deepMindEquations_iff_reducedEquations
      p.a p.b p.phi p.theta).2 (by simpa [reducedParams] using heq)
  have hspec : DeepMindABPhiThetaSpec p.a p.b p.phi p.theta :=
    ⟨by simpa [reducedParams] using hdom, hdeep⟩
  have htwo : TwoAngleSpec p.phi p.theta :=
    (exists_deepMindSpec_iff_twoAngleSpec p.phi p.theta).1
      ⟨p.a, p.b, hspec⟩
  have hmem := hangle p.phi p.theta htwo
  have hA := a_eq_reconstructed_of_physical_and_equations hspec.1 hspec.2
  have hB := b_eq_reconstructed_of_physical_and_equations hspec.1 hspec.2
  change
    reducedParams
      (reconstructedA p.phi p.theta) (reconstructedB p.phi p.theta)
      p.phi p.theta ∈ Reduced.box at hmem
  rw [← hA, ← hB] at hmem
  simpa [reconstructedParams, reducedParams] using hmem

/-- Terminal E02 bridge: the exact DeepMind-shaped uniqueness theorem now
requires only the compact two-angle enclosure theorem. -/
theorem deepMindABPhiTheta_existsUnique_of_twoAngleEnclosure
    (hangle : TwoAngleEnclosureTarget) :
    ∃! ABphiTheta : ℝ × ℝ × ℝ × ℝ,
      DeepMindABPhiThetaSpec
        ABphiTheta.1 ABphiTheta.2.1 ABphiTheta.2.2.1 ABphiTheta.2.2.2 :=
  deepMindABPhiTheta_existsUnique_of_globalEnclosure
    (globalEnclosureTarget_of_twoAngleEnclosure hangle)

end PartE
end GerverSofa
