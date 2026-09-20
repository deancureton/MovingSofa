import GerverSofa.KernelOnly.PartE.FiniteCoverReplay

/-!
# Part E21F: local two-angle Krawczyk closure repair

The residual-only cover becomes inefficient close to the certified Gerver
zero.  This module replaces arbitrarily deep subdivision there by a single
two-dimensional contraction certificate on a deliberately wider rational
box.  The wide box contains both the exact projection of `Reduced.box` and
the complete unresolved E19 tail.

The resulting theorem identifies every smooth residual zero in the wide box
with the already certified Part A reduced solution.  A terminal composition
theorem therefore needs interval rejection only outside this wide local box.
-/

noncomputable section

namespace GerverSofa
namespace PartE

open LeanCert.Core
open LeanCert.Engine
open PartALeanCert

/-! ## Concrete two-dimensional contraction data -/

/-- Local angle box containing the complete unresolved E20 tail and the exact
angle projection of `Reduced.box`.  E21F narrows the exploratory E21 box to
the region actually required by the recorded E20 extrema. -/
def localAngleX : Fin 2 → IntervalRat := ![
  ⟨391 / 10000, 157 / 4000, by norm_num⟩,
  ⟨68113 / 100000, 34069 / 50000, by norm_num⟩
]

/-- Rational center near the already certified Gerver zero. -/
def localAngleCenter : Fin 2 → ℚ := ![
  3917736479 / 100000000000,
  681301509383 / 1000000000000
]

/-- Rational approximation to the inverse Jacobian of the two scaled
residuals at `localAngleCenter`. -/
def localAngleY : Matrix (Fin 2) (Fin 2) ℚ := ![
  ![-2886 / 10000, -1481 / 10000],
  ![6267 / 10000, -27218 / 10000]
]

def localAngleCfg : EvalConfig := {}

/-- Contraction constant used by the checked local uniqueness theorem. -/
def localAngleQ : ℚ := 3 / 10

def localAnglePJ : Matrix (Fin 2) (Fin 2) IntervalRat :=
  preconditionedJacobian localAngleY
    (intervalJacobian scaledResidualExpr localAngleX localAngleCfg)

def localAngleImage (i : Fin 2) : IntervalRat :=
  imageEnclosureWithQ scaledResidualExpr localAngleX localAngleCenter
    localAngleY localAngleCfg localAngleQ i

theorem localAngleQ_nonneg : (0 : ℚ) ≤ localAngleQ := by
  norm_num [localAngleQ]

theorem localAngleQ_lt_one : localAngleQ < (1 : ℚ) := by
  norm_num [localAngleQ]

theorem localAngleCenter_mem :
    FinBoxMem (fun i : Fin 2 => (localAngleCenter i : ℝ)) localAngleX := by
  intro i
  fin_cases i <;>
    simp [localAngleCenter, localAngleX, IntervalRat.mem_def] <;>
    norm_num

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem localAngle_bound_lt :
    intervalMatrixBound localAnglePJ < localAngleQ := by
  decide +kernel

theorem localAngle_bound_le :
    intervalMatrixBound localAnglePJ ≤ localAngleQ :=
  localAngle_bound_lt.le

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem localAngle_image_zero_inside :
    intervalStrictInside (localAngleImage (0 : Fin 2))
      (localAngleX (0 : Fin 2)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem localAngle_image_one_inside :
    intervalStrictInside (localAngleImage (1 : Fin 2))
      (localAngleX (1 : Fin 2)) = true := by
  decide +kernel

theorem localAngle_images_inside :
    ∀ i : Fin 2,
      intervalStrictInside (localAngleImage i) (localAngleX i) = true := by
  intro i
  fin_cases i
  · exact localAngle_image_zero_inside
  · exact localAngle_image_one_inside

/-- Kernel-checked existence and uniqueness of a common scaled-residual zero
throughout the complete wide local box. -/
theorem localAngle_unique_scaled :
    ∃! u, FinBoxMem u localAngleX ∧ SystemZero scaledResidualExpr u := by
  exact uniqueSystemZero_of_certified_contraction
    scaledResidualExpr scaledResidualExpr_supported
    localAngleX localAngleCenter localAngleCenter_mem
    localAngleY localAngleCfg localAngleQ
    localAngleQ_nonneg localAngleQ_lt_one
    (by simpa [localAnglePJ] using localAngle_bound_le)
    (by simpa [localAngleImage] using localAngle_images_inside)

/-! ## Semantic bridge to named angles and the Part A solution -/

def localAngleCell : AngleCell :=
  ⟨localAngleX (0 : Fin 2), localAngleX (1 : Fin 2)⟩

def localAngleVector (phi theta : ℝ) : Fin 2 → ℝ := ![phi, theta]

theorem localAngleVector_mem_iff (phi theta : ℝ) :
    FinBoxMem (localAngleVector phi theta) localAngleX ↔
      localAngleCell.Contains phi theta := by
  constructor
  · intro h
    exact ⟨by simpa [localAngleVector, localAngleCell] using h (0 : Fin 2),
      by simpa [localAngleVector, localAngleCell] using h (1 : Fin 2)⟩
  · rintro ⟨hphi, htheta⟩ i
    fin_cases i
    · simpa [localAngleVector, localAngleCell] using hphi
    · simpa [localAngleVector, localAngleCell] using htheta

theorem localAngleVector_systemZero_iff (phi theta : ℝ) :
    SystemZero scaledResidualExpr (localAngleVector phi theta) ↔
      scaledResidualOne phi theta = 0 ∧ scaledResidualTwo phi theta = 0 := by
  constructor
  · intro h
    constructor
    · have hzero := h (0 : Fin 2)
      change evalFin (scaledResidualExpr (0 : Fin 2))
        (localAngleVector phi theta) = 0 at hzero
      simpa [localAngleVector, scaledResidualExpr_eval_zero] using hzero
    · have hzero := h (1 : Fin 2)
      change evalFin (scaledResidualExpr (1 : Fin 2))
        (localAngleVector phi theta) = 0 at hzero
      simpa [localAngleVector, scaledResidualExpr_eval_one] using hzero
  · rintro ⟨hzeroOne, hzeroTwo⟩ i
    fin_cases i
    · change evalFin (scaledResidualExpr (0 : Fin 2))
        (localAngleVector phi theta) = 0
      simpa [localAngleVector, scaledResidualExpr_eval_zero] using hzeroOne
    · change evalFin (scaledResidualExpr (1 : Fin 2))
        (localAngleVector phi theta) = 0
      simpa [localAngleVector, scaledResidualExpr_eval_one] using hzeroTwo

def certifiedReducedSolution : Reduced.Params :=
  PartALeanCert.reducedCertifiedUniqueSolution.solution

theorem certifiedReducedSolution_mem :
    certifiedReducedSolution ∈ Reduced.box := by
  exact PartALeanCert.reducedCertifiedUniqueSolution.solution_mem

theorem certifiedReducedSolution_satisfies :
    Reduced.Equations certifiedReducedSolution := by
  exact PartALeanCert.reducedCertifiedUniqueSolution.satisfies

/-- The Part A solution's angle pair lies strictly inside the wide local
box, by exact rational endpoint comparison. -/
theorem certifiedAngles_mem_localAngleCell :
    localAngleCell.Contains
      certifiedReducedSolution.phi certifiedReducedSolution.theta := by
  have hp := certifiedReducedSolution_mem
  dsimp [Reduced.box, qR] at hp
  rcases hp with
    ⟨_haLo, _haHi, _hbLo, _hbHi,
      hphiLo, hphiHi, hthetaLo, hthetaHi⟩
  change
    certifiedReducedSolution.phi ∈ localAngleX (0 : Fin 2) ∧
      certifiedReducedSolution.theta ∈ localAngleX (1 : Fin 2)
  constructor
  · change
      (((391 / 10000 : ℚ) : ℝ) ≤ certifiedReducedSolution.phi ∧
        certifiedReducedSolution.phi ≤ ((157 / 4000 : ℚ) : ℝ))
    constructor
    · norm_num at hphiLo ⊢
      linarith
    · norm_num at hphiHi ⊢
      linarith
  · change
      (((68113 / 100000 : ℚ) : ℝ) ≤ certifiedReducedSolution.theta ∧
        certifiedReducedSolution.theta ≤ ((34069 / 50000 : ℚ) : ℝ))
    constructor
    · norm_num at hthetaLo ⊢
      linarith
    · norm_num at hthetaHi ⊢
      linarith

theorem certifiedAngles_mem_localAngleX :
    FinBoxMem
      (localAngleVector certifiedReducedSolution.phi
        certifiedReducedSolution.theta) localAngleX :=
  (localAngleVector_mem_iff _ _).2 certifiedAngles_mem_localAngleCell

theorem certifiedAngles_systemZero :
    SystemZero scaledResidualExpr
      (localAngleVector certifiedReducedSolution.phi
        certifiedReducedSolution.theta) := by
  have hdeep : DeepMindABPhiThetaSpec
      certifiedReducedSolution.a certifiedReducedSolution.b
      certifiedReducedSolution.phi certifiedReducedSolution.theta :=
    deepMindSpec_of_mem_reducedBox_and_equations
      certifiedReducedSolution_mem certifiedReducedSolution_satisfies
  have htwo : TwoAngleSpec
      certifiedReducedSolution.phi certifiedReducedSolution.theta :=
    (exists_deepMindSpec_iff_twoAngleSpec
      certifiedReducedSolution.phi certifiedReducedSolution.theta).1
      ⟨certifiedReducedSolution.a, certifiedReducedSolution.b, hdeep⟩
  have hscaled :=
    (twoAngleSpec_iff_scaledTwoAngleSpec
      certifiedReducedSolution.phi certifiedReducedSolution.theta).1 htwo
  rcases hscaled with ⟨_hdom, _hden, _hA, _hB, hzeroOne, hzeroTwo⟩
  exact (localAngleVector_systemZero_iff _ _).2 ⟨hzeroOne, hzeroTwo⟩

/-- Every smooth physical solution in the wide local cell reconstructs to
the already certified Part A solution and hence belongs to `Reduced.box`. -/
theorem reconstructedParams_mem_reducedBox_of_mem_localAngleCell
    {phi theta : ℝ} (hspec : ScaledTwoAngleSpec phi theta)
    (hlocal : localAngleCell.Contains phi theta) :
    reconstructedParams phi theta ∈ Reduced.box := by
  have hmem : FinBoxMem (localAngleVector phi theta) localAngleX :=
    (localAngleVector_mem_iff phi theta).2 hlocal
  have hzero : SystemZero scaledResidualExpr (localAngleVector phi theta) :=
    (localAngleVector_systemZero_iff phi theta).2
      ⟨hspec.2.2.2.2.1, hspec.2.2.2.2.2⟩
  have heq :
      localAngleVector phi theta =
        localAngleVector certifiedReducedSolution.phi
          certifiedReducedSolution.theta :=
    localAngle_unique_scaled.unique ⟨hmem, hzero⟩
      ⟨certifiedAngles_mem_localAngleX, certifiedAngles_systemZero⟩
  have hphi : phi = certifiedReducedSolution.phi := by
    have h := congrFun heq (0 : Fin 2)
    simpa [localAngleVector] using h
  have htheta : theta = certifiedReducedSolution.theta := by
    have h := congrFun heq (1 : Fin 2)
    simpa [localAngleVector] using h
  have hdeep : DeepMindABPhiThetaSpec
      certifiedReducedSolution.a certifiedReducedSolution.b
      certifiedReducedSolution.phi certifiedReducedSolution.theta :=
    deepMindSpec_of_mem_reducedBox_and_equations
      certifiedReducedSolution_mem certifiedReducedSolution_satisfies
  have hA := a_eq_reconstructed_of_physical_and_equations hdeep.1 hdeep.2
  have hB := b_eq_reconstructed_of_physical_and_equations hdeep.1 hdeep.2
  rw [hphi, htheta]
  change reducedParams
      (reconstructedA certifiedReducedSolution.phi
        certifiedReducedSolution.theta)
      (reconstructedB certifiedReducedSolution.phi
        certifiedReducedSolution.theta)
      certifiedReducedSolution.phi certifiedReducedSolution.theta ∈ Reduced.box
  rw [← hA, ← hB]
  simpa [reducedParams] using certifiedReducedSolution_mem

/-! ## Terminal composition with rejection only outside the wide box -/

def WideLocalReconstructionEnclosureTarget : Prop :=
  ∀ phi theta : ℝ,
    ScaledTwoAngleSpec phi theta →
    localAngleCell.Contains phi theta →
    reconstructedParams phi theta ∈ Reduced.box

theorem wideLocalReconstructionEnclosureTarget :
    WideLocalReconstructionEnclosureTarget := by
  intro phi theta hspec hlocal
  exact reconstructedParams_mem_reducedBox_of_mem_localAngleCell hspec hlocal

/-! Machine-readable replay markers consumed by the E21 runner. -/

/- Exact diagnostic values are printed even if a later repair run stops at a
closed Boolean theorem. -/
#eval intervalMatrixBound localAnglePJ
#eval localAngleImage (0 : Fin 2)
#eval localAngleImage (1 : Fin 2)

#eval if intervalMatrixBound localAnglePJ < localAngleQ then
  "E21F_CONTRACTION_BOUND_LT_Q=true" else
  "E21F_CONTRACTION_BOUND_LT_Q=false"

#eval if intervalStrictInside (localAngleImage (0 : Fin 2))
    (localAngleX (0 : Fin 2)) = true then
  "E21F_IMAGE_0_INSIDE=true" else "E21F_IMAGE_0_INSIDE=false"

#eval if intervalStrictInside (localAngleImage (1 : Fin 2))
    (localAngleX (1 : Fin 2)) = true then
  "E21F_IMAGE_1_INSIDE=true" else "E21F_IMAGE_1_INSIDE=false"

end PartE
end GerverSofa
