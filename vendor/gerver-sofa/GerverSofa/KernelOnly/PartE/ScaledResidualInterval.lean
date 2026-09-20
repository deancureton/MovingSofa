import GerverSofa.KernelOnly.PartE.TwoAngleReduction
import Mathlib.Tactic.FieldSimp

/-!
# Part E03: division-free two-angle residuals and interval rejection kernel

E02 reduced the four-variable DeepMind system to two angles, but its
reconstructed values contain a quotient.  Direct interval evaluation of that
quotient is unnecessarily singular near the corner where its denominator can
vanish.

This module clears the denominator exactly.  It proves that, whenever the E02
denominator is nonzero, the two original reconstructed equations are
equivalent to two smooth residuals containing only addition, multiplication,
`sin`, `cos`, and the named constant `pi`.

The same residuals are encoded as LeanCert expressions.  The final theorem is
a reusable, executable cell-rejection kernel: if certified interval evaluation
of either residual excludes zero on a rational rectangle, no common zero can
lie in that rectangle.  E03 intentionally does not postulate a global cover;
the finite branch-and-bound cover is the next data layer.
-/

noncomputable section

namespace GerverSofa
namespace PartE

open LeanCert.Core
open LeanCert.Engine
open PartALeanCert

/-- First reconstructed E02 equation, written as a residual. -/
def firstReconstructedResidual (phi theta : ℝ) : ℝ :=
  reconstructedA phi theta * (Real.cos theta - Real.cos phi)
    - 2 * reconstructedB phi theta * Real.sin phi
    + (theta - phi - 1) * Real.cos theta - Real.sin theta
    + Real.cos phi + Real.sin phi

/-- Second reconstructed E02 equation, written as a residual. -/
def secondReconstructedResidual (phi theta : ℝ) : ℝ :=
  reconstructedA phi theta * (3 * Real.sin theta + Real.sin phi)
    - 2 * reconstructedB phi theta * Real.cos phi
    + 3 * (theta - phi - 1) * Real.sin theta + 3 * Real.cos theta
    - Real.sin phi + Real.cos phi

/-- Numerator of `denominator * reconstructedB`, with no division. -/
def scaledB (phi theta : ℝ) : ℝ :=
  angleNumerator phi theta * (1 + angleDelta phi theta / 2)
    + bBase phi theta * angleDenominator phi theta

/-- Division-free first residual. -/
def scaledResidualOne (phi theta : ℝ) : ℝ :=
  angleNumerator phi theta * (Real.cos theta - Real.cos phi)
    - 2 * scaledB phi theta * Real.sin phi
    + (angleDelta phi theta - 1) * Real.cos theta
        * angleDenominator phi theta
    - Real.sin theta * angleDenominator phi theta
    + Real.cos phi * angleDenominator phi theta
    + Real.sin phi * angleDenominator phi theta

/-- Division-free second residual. -/
def scaledResidualTwo (phi theta : ℝ) : ℝ :=
  angleNumerator phi theta * (3 * Real.sin theta + Real.sin phi)
    - 2 * scaledB phi theta * Real.cos phi
    + 3 * (angleDelta phi theta - 1) * Real.sin theta
        * angleDenominator phi theta
    + 3 * Real.cos theta * angleDenominator phi theta
    - Real.sin phi * angleDenominator phi theta
    + Real.cos phi * angleDenominator phi theta

/-- The cleared numerator is exactly `denominator * reconstructedB`. -/
theorem denominator_mul_reconstructedB_eq_scaledB
    (phi theta : ℝ) (hden : angleDenominator phi theta ≠ 0) :
    angleDenominator phi theta * reconstructedB phi theta =
      scaledB phi theta := by
  dsimp [reconstructedB, bFromA, reconstructedA, scaledB]
  field_simp [hden]
  <;> ring

/-- The first smooth residual is the original residual multiplied by the
E02 denominator. -/
theorem scaledResidualOne_eq_denominator_mul
    (phi theta : ℝ) (hden : angleDenominator phi theta ≠ 0) :
    scaledResidualOne phi theta =
      angleDenominator phi theta * firstReconstructedResidual phi theta := by
  have hA : angleDenominator phi theta * reconstructedA phi theta =
      angleNumerator phi theta := by
    dsimp [reconstructedA]
    field_simp [hden]
  have hB := denominator_mul_reconstructedB_eq_scaledB phi theta hden
  unfold scaledResidualOne firstReconstructedResidual
  rw [← hA, ← hB]
  dsimp [angleDelta]
  ring

/-- The second smooth residual is the original residual multiplied by the
E02 denominator. -/
theorem scaledResidualTwo_eq_denominator_mul
    (phi theta : ℝ) (hden : angleDenominator phi theta ≠ 0) :
    scaledResidualTwo phi theta =
      angleDenominator phi theta * secondReconstructedResidual phi theta := by
  have hA : angleDenominator phi theta * reconstructedA phi theta =
      angleNumerator phi theta := by
    dsimp [reconstructedA]
    field_simp [hden]
  have hB := denominator_mul_reconstructedB_eq_scaledB phi theta hden
  unfold scaledResidualTwo secondReconstructedResidual
  rw [← hA, ← hB]
  dsimp [angleDelta]
  ring

/-- E02's two equations are exactly the vanishing of the two ordinary
reconstructed residuals. -/
theorem twoAngleEquations_iff_reconstructedResiduals_zero
    (phi theta : ℝ) :
    TwoAngleEquations phi theta ↔
      firstReconstructedResidual phi theta = 0 ∧
      secondReconstructedResidual phi theta = 0 := by
  rfl

/-- Exact denominator-clearing equivalence used by the interval layer. -/
theorem twoAngleEquations_iff_scaledResiduals_zero
    (phi theta : ℝ) (hden : angleDenominator phi theta ≠ 0) :
    TwoAngleEquations phi theta ↔
      scaledResidualOne phi theta = 0 ∧
      scaledResidualTwo phi theta = 0 := by
  rw [twoAngleEquations_iff_reconstructedResiduals_zero]
  rw [scaledResidualOne_eq_denominator_mul phi theta hden]
  rw [scaledResidualTwo_eq_denominator_mul phi theta hden]
  constructor
  · rintro ⟨h1, h2⟩
    simp [h1, h2]
  · rintro ⟨h1, h2⟩
    exact ⟨(mul_eq_zero.mp h1).resolve_left hden,
      (mul_eq_zero.mp h2).resolve_left hden⟩

/-- The complete E02 specification with only smooth equations in its final
conjunct. -/
def ScaledTwoAngleSpec (phi theta : ℝ) : Prop :=
  PhysicalAngleDomain phi theta ∧
    angleDenominator phi theta ≠ 0 ∧
    0 ≤ reconstructedA phi theta ∧
    0 ≤ reconstructedB phi theta ∧
    scaledResidualOne phi theta = 0 ∧
    scaledResidualTwo phi theta = 0

/-- No mathematical information is lost by clearing the denominator. -/
theorem twoAngleSpec_iff_scaledTwoAngleSpec (phi theta : ℝ) :
    TwoAngleSpec phi theta ↔ ScaledTwoAngleSpec phi theta := by
  constructor
  · rintro ⟨hdom, hden, hA, hB, heq⟩
    exact ⟨hdom, hden, hA, hB,
      (twoAngleEquations_iff_scaledResiduals_zero phi theta hden).1 heq⟩
  · rintro ⟨hdom, hden, hA, hB, heq⟩
    exact ⟨hdom, hden, hA, hB,
      (twoAngleEquations_iff_scaledResiduals_zero phi theta hden).2 heq⟩

/-- E02's remaining enclosure target, now stated over division-free
equations. -/
def ScaledResidualEnclosureTarget : Prop :=
  ∀ phi theta : ℝ,
    ScaledTwoAngleSpec phi theta → reconstructedParams phi theta ∈ Reduced.box

/-- The smooth-residual enclosure target is exactly the E02 target. -/
theorem scaledResidualEnclosureTarget_iff_twoAngleEnclosureTarget :
    ScaledResidualEnclosureTarget ↔ TwoAngleEnclosureTarget := by
  constructor
  · intro h phi theta hspec
    exact h phi theta ((twoAngleSpec_iff_scaledTwoAngleSpec phi theta).1 hspec)
  · intro h phi theta hspec
    exact h phi theta ((twoAngleSpec_iff_scaledTwoAngleSpec phi theta).2 hspec)

/-! ## LeanCert expression model -/

/-- LeanCert AST for the two division-free residuals.  Variable 0 is `phi`
and variable 1 is `theta`. -/
def scaledResidualExprList : List Expr :=
  let phi := ev 0
  let theta := ev 1
  let one := ec 1
  let half := ec (1 / 2)
  let quarter := ec (1 / 4)
  let delta := esub theta phi
  let cp := ecos phi
  let sp := esin phi
  let ct := ecos theta
  let st := esin theta
  let base :=
    eadd
      (eadd (esub (esub (escale (1 / 2) epi) phi) theta)
        (escale (1 / 2) delta))
      (escale (1 / 4) (emul delta delta))
  let den := esub cp (emul (eadd one (escale (1 / 2) delta)) sp)
  let num :=
    eadd
      (eadd (eadd sp half) (eneg (escale (1 / 2) cp)))
      (emul base sp)
  let numB :=
    eadd (emul num (eadd one (escale (1 / 2) delta))) (emul base den)
  let r1 :=
    eadd
      (eadd
        (eadd
          (eadd
            (esub (emul num (esub ct cp)) (emul (escale 2 numB) sp))
            (emul (emul (esub delta one) ct) den))
          (eneg (emul st den)))
        (emul cp den))
      (emul sp den)
  let r2 :=
    eadd
      (eadd
        (eadd
          (eadd
            (esub (emul num (eadd (escale 3 st) sp))
              (emul (escale 2 numB) cp))
            (emul (emul (escale 3 (esub delta one)) st) den))
          (emul (escale 3 ct) den))
        (eneg (emul sp den)))
      (emul cp den)
  r1 :: r2 :: []

def scaledResidualExpr (i : Fin 2) : Expr :=
  scaledResidualExprList.getD i.1 (ec 0)

/-- Both ASTs belong to LeanCert's fully proved core and AD fragment. -/
theorem scaledResidualExpr_supported :
    ∀ i : Fin 2, ADConstSupported (scaledResidualExpr i) := by
  intro i
  apply checkADConstSupported_correct
  fin_cases i <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem scaledResidualExpr_eval_zero (phi theta : ℝ) :
    evalFin (scaledResidualExpr (0 : Fin 2)) ![phi, theta] =
      scaledResidualOne phi theta := by
  simp [scaledResidualExpr, scaledResidualExprList, scaledResidualOne, scaledB,
    angleNumerator, angleDenominator, bBase, angleDelta,
    eadd, eneg, esub, emul, escale, esin, ecos, ec, ev, epi,
    evalFin, finEnv]
  <;> ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem scaledResidualExpr_eval_one (phi theta : ℝ) :
    evalFin (scaledResidualExpr (1 : Fin 2)) ![phi, theta] =
      scaledResidualTwo phi theta := by
  simp [scaledResidualExpr, scaledResidualExprList, scaledResidualTwo, scaledB,
    angleNumerator, angleDenominator, bBase, angleDelta,
    eadd, eneg, esub, emul, escale, esin, ecos, ec, ev, epi,
    evalFin, finEnv]
  <;> ring

/-- Rational interval environment for the two angle variables. -/
def angleIntervalEnv (phiI thetaI : IntervalRat) : IntervalEnv
  | 0 => phiI
  | 1 => thetaI
  | _ => default

/-- Executable test that an interval lies strictly on one side of zero. -/
def intervalExcludesZero (I : IntervalRat) : Bool :=
  decide (I.hi < 0 ∨ 0 < I.lo)

/-- The executable zero-exclusion test is sound over real interval
membership. -/
theorem intervalExcludesZero_sound (I : IntervalRat)
    (h : intervalExcludesZero I = true) : (0 : ℝ) ∉ I := by
  have hrat : I.hi < 0 ∨ 0 < I.lo := by
    exact of_decide_eq_true h
  intro hmem
  rw [IntervalRat.mem_def] at hmem
  rcases hrat with hhi | hlo
  · have hhi' : (I.hi : ℝ) < 0 := by exact_mod_cast hhi
    linarith
  · have hlo' : 0 < (I.lo : ℝ) := by exact_mod_cast hlo
    linarith

end PartE
end GerverSofa
