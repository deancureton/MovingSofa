import GerverSofa.KernelOnly.PartE.LocalTwoAngleKrawczykClosure
import Mathlib.Tactic

/-!
# Part E22F foundation: adaptive global cover

This module replaces the probe-only upper-wedge files by one kernel-reducible
adaptive checker.  Starting from the rational square `[0, 4/5]^2`, it prunes
cells which are outside the physical triangle, cells wholly contained in the
wide E21 local box, and cells rejected by the certified E03 interval kernel.
Every remaining cell is split into four exact rational children.  Depth 18 is
the depth reached by the final E20 refinement around the Gerver root.

The soundness theorem is independent of the closed computation.  E22F compiles
the depth-18 Boolean certificate in sixty-four independent depth-15 modules;
`ParallelAdaptiveGlobalCoverClosure` recombines them without recomputation.
-/

noncomputable section

namespace GerverSofa
namespace PartE

open LeanCert.Core

def angleMid (i : IntervalRat) : ℚ := (i.lo + i.hi) / 2

def intervalLow (i : IntervalRat) : IntervalRat :=
  ⟨i.lo, angleMid i, by
    dsimp [angleMid]
    linarith [i.le]⟩

def intervalHigh (i : IntervalRat) : IntervalRat :=
  ⟨angleMid i, i.hi, by
    dsimp [angleMid]
    linarith [i.le]⟩

def childLL (cell : AngleCell) : AngleCell :=
  ⟨intervalLow cell.phiI, intervalLow cell.thetaI⟩

def childLH (cell : AngleCell) : AngleCell :=
  ⟨intervalLow cell.phiI, intervalHigh cell.thetaI⟩

def childHL (cell : AngleCell) : AngleCell :=
  ⟨intervalHigh cell.phiI, intervalLow cell.thetaI⟩

def childHH (cell : AngleCell) : AngleCell :=
  ⟨intervalHigh cell.phiI, intervalHigh cell.thetaI⟩

/-- A rational cell lies strictly above the physical half-plane `phi ≤ theta`.
The strict comparison deliberately keeps all cells touching the diagonal. -/
def physicallyIrrelevant (cell : AngleCell) : Bool :=
  decide (cell.thetaI.hi < cell.phiI.lo)

/-- Every point of the rational cell lies in the wide E21 local box. -/
def cellInsideLocal (cell : AngleCell) : Bool :=
  decide (
    localAngleCell.phiI.lo ≤ cell.phiI.lo ∧
    cell.phiI.hi ≤ localAngleCell.phiI.hi ∧
    localAngleCell.thetaI.lo ≤ cell.thetaI.lo ∧
    cell.thetaI.hi ≤ localAngleCell.thetaI.hi)

/-- Adaptive four-way replay.  A node closes when it is irrelevant, local, or
rejected.  Otherwise all four rational midpoint children must close. -/
def adaptiveCoverCheck : Nat → AngleCell → Bool
  | 0, cell =>
      if physicallyIrrelevant cell = true then true
      else if cellInsideLocal cell = true then true
      else cell.rejected
  | depth + 1, cell =>
      if physicallyIrrelevant cell = true then true
      else if cellInsideLocal cell = true then true
      else if cell.rejected = true then true
      else
        adaptiveCoverCheck depth (childLL cell) &&
          (adaptiveCoverCheck depth (childLH cell) &&
            (adaptiveCoverCheck depth (childHL cell) &&
              adaptiveCoverCheck depth (childHH cell)))

theorem physicallyIrrelevant_no_physical_point
    (cell : AngleCell) (phi theta : ℝ)
    (hirr : physicallyIrrelevant cell = true)
    (hdom : PhysicalAngleDomain phi theta)
    (hmem : cell.Contains phi theta) : False := by
  have hrat : cell.thetaI.hi < cell.phiI.lo := by
    exact of_decide_eq_true hirr
  have hreal : (cell.thetaI.hi : ℝ) < (cell.phiI.lo : ℝ) := by
    exact_mod_cast hrat
  change phi ∈ cell.phiI ∧ theta ∈ cell.thetaI at hmem
  simp only [IntervalRat.mem_def] at hmem
  linarith [hdom.2.1, hmem.1.1, hmem.2.2]

theorem cellInsideLocal_sound
    (cell : AngleCell) (phi theta : ℝ)
    (hlocal : cellInsideLocal cell = true)
    (hmem : cell.Contains phi theta) :
    localAngleCell.Contains phi theta := by
  have hb :
      localAngleCell.phiI.lo ≤ cell.phiI.lo ∧
      cell.phiI.hi ≤ localAngleCell.phiI.hi ∧
      localAngleCell.thetaI.lo ≤ cell.thetaI.lo ∧
      cell.thetaI.hi ≤ localAngleCell.thetaI.hi := by
    exact of_decide_eq_true hlocal
  change phi ∈ cell.phiI ∧ theta ∈ cell.thetaI at hmem
  change phi ∈ localAngleCell.phiI ∧ theta ∈ localAngleCell.thetaI
  simp only [IntervalRat.mem_def] at hmem ⊢
  have hpLo : (localAngleCell.phiI.lo : ℝ) ≤ (cell.phiI.lo : ℝ) := by
    exact_mod_cast hb.1
  have hpHi : (cell.phiI.hi : ℝ) ≤ (localAngleCell.phiI.hi : ℝ) := by
    exact_mod_cast hb.2.1
  have htLo : (localAngleCell.thetaI.lo : ℝ) ≤ (cell.thetaI.lo : ℝ) := by
    exact_mod_cast hb.2.2.1
  have htHi : (cell.thetaI.hi : ℝ) ≤ (localAngleCell.thetaI.hi : ℝ) := by
    exact_mod_cast hb.2.2.2
  exact ⟨⟨hpLo.trans hmem.1.1, hmem.1.2.trans hpHi⟩,
    ⟨htLo.trans hmem.2.1, hmem.2.2.trans htHi⟩⟩

/-- Every real point in a parent cell belongs to at least one of its four
closed midpoint children. -/
theorem contains_some_midpoint_child
    (cell : AngleCell) (phi theta : ℝ)
    (hmem : cell.Contains phi theta) :
    (childLL cell).Contains phi theta ∨
      (childLH cell).Contains phi theta ∨
      (childHL cell).Contains phi theta ∨
      (childHH cell).Contains phi theta := by
  change phi ∈ cell.phiI ∧ theta ∈ cell.thetaI at hmem
  simp only [IntervalRat.mem_def] at hmem
  by_cases hp : phi ≤ (angleMid cell.phiI : ℝ)
  · by_cases ht : theta ≤ (angleMid cell.thetaI : ℝ)
    · left
      change phi ∈ intervalLow cell.phiI ∧ theta ∈ intervalLow cell.thetaI
      simp only [IntervalRat.mem_def, intervalLow]
      exact ⟨⟨hmem.1.1, hp⟩, ⟨hmem.2.1, ht⟩⟩
    · right; left
      have ht' : (angleMid cell.thetaI : ℝ) ≤ theta :=
        le_of_lt (lt_of_not_ge ht)
      change phi ∈ intervalLow cell.phiI ∧ theta ∈ intervalHigh cell.thetaI
      simp only [IntervalRat.mem_def, intervalLow, intervalHigh]
      exact ⟨⟨hmem.1.1, hp⟩, ⟨ht', hmem.2.2⟩⟩
  · have hp' : (angleMid cell.phiI : ℝ) ≤ phi :=
      le_of_lt (lt_of_not_ge hp)
    by_cases ht : theta ≤ (angleMid cell.thetaI : ℝ)
    · right; right; left
      change phi ∈ intervalHigh cell.phiI ∧ theta ∈ intervalLow cell.thetaI
      simp only [IntervalRat.mem_def, intervalLow, intervalHigh]
      exact ⟨⟨hp', hmem.1.2⟩, ⟨hmem.2.1, ht⟩⟩
    · right; right; right
      have ht' : (angleMid cell.thetaI : ℝ) ≤ theta :=
        le_of_lt (lt_of_not_ge ht)
      change phi ∈ intervalHigh cell.phiI ∧ theta ∈ intervalHigh cell.thetaI
      simp only [IntervalRat.mem_def, intervalHigh]
      exact ⟨⟨hp', hmem.1.2⟩, ⟨ht', hmem.2.2⟩⟩

/-- Semantic soundness of the adaptive Boolean replay. -/
theorem adaptiveCoverCheck_no_common_zero
    (depth : Nat) (cell : AngleCell)
    (hcheck : adaptiveCoverCheck depth cell = true)
    (phi theta : ℝ)
    (hdom : PhysicalAngleDomain phi theta)
    (hmem : cell.Contains phi theta)
    (houtside : ¬ localAngleCell.Contains phi theta) :
    ¬ (scaledResidualOne phi theta = 0 ∧
      scaledResidualTwo phi theta = 0) := by
  induction depth generalizing cell with
  | zero =>
      by_cases hirr : physicallyIrrelevant cell = true
      · exact (physicallyIrrelevant_no_physical_point
          cell phi theta hirr hdom hmem).elim
      by_cases hlocal : cellInsideLocal cell = true
      · exact (houtside (cellInsideLocal_sound
          cell phi theta hlocal hmem)).elim
      have hrejected : cell.rejected = true := by
        simpa [adaptiveCoverCheck, hirr, hlocal] using hcheck
      exact AngleCell.no_common_zero_of_rejected
        cell phi theta hmem (cfg := {}) hrejected
  | succ depth ih =>
      by_cases hirr : physicallyIrrelevant cell = true
      · exact (physicallyIrrelevant_no_physical_point
          cell phi theta hirr hdom hmem).elim
      by_cases hlocal : cellInsideLocal cell = true
      · exact (houtside (cellInsideLocal_sound
          cell phi theta hlocal hmem)).elim
      by_cases hrejected : cell.rejected = true
      · exact AngleCell.no_common_zero_of_rejected
          cell phi theta hmem (cfg := {}) hrejected
      have hchildren :
          adaptiveCoverCheck depth (childLL cell) = true ∧
          (adaptiveCoverCheck depth (childLH cell) = true ∧
          (adaptiveCoverCheck depth (childHL cell) = true ∧
            adaptiveCoverCheck depth (childHH cell) = true)) := by
        simpa [adaptiveCoverCheck, hirr, hlocal, hrejected,
          Bool.and_eq_true] using hcheck
      rcases contains_some_midpoint_child cell phi theta hmem with
        hll | hlh | hhl | hhh
      · exact ih (cell := childLL cell) hchildren.1 hll
      · exact ih (cell := childLH cell) hchildren.2.1 hlh
      · exact ih (cell := childHL cell) hchildren.2.2.1 hhl
      · exact ih (cell := childHH cell) hchildren.2.2.2 hhh

/-- Rational root containing the complete physical angle triangle. -/
def globalAngleRoot : AngleCell :=
  ⟨⟨0, 4 / 5, by norm_num⟩, ⟨0, 4 / 5, by norm_num⟩⟩

theorem physicalAngleDomain_mem_globalAngleRoot
    (phi theta : ℝ) (hdom : PhysicalAngleDomain phi theta) :
    globalAngleRoot.Contains phi theta := by
  have hpi := ExactReplay.piI_contains_pi
  have hhi : Real.pi ≤ (ExactReplay.piI.hi : ℝ) := hpi.2
  have h32 : (ExactReplay.piI.hi : ℝ) < (16 / 5 : ℝ) := by
    norm_num [ExactReplay.piI, ExactReplay.q]
  have htheta : theta < (4 / 5 : ℝ) := by
    linarith [hdom.2.2]
  change phi ∈ (⟨0, 4 / 5, by norm_num⟩ : IntervalRat) ∧
    theta ∈ (⟨0, 4 / 5, by norm_num⟩ : IntervalRat)
  simp only [IntervalRat.mem_def]
  norm_num at ⊢
  exact ⟨⟨hdom.1, (hdom.2.1.trans htheta.le)⟩,
    ⟨hdom.1.trans hdom.2.1, htheta.le⟩⟩

/-- A parent closes whenever its four children close.  This lemma permits the
depth-18 computation to be compiled in independent shards without changing
the kernel proposition that is certified. -/
theorem adaptiveCoverCheck_succ_of_children
    (depth : Nat) (cell : AngleCell)
    (hLL : adaptiveCoverCheck depth (childLL cell) = true)
    (hLH : adaptiveCoverCheck depth (childLH cell) = true)
    (hHL : adaptiveCoverCheck depth (childHL cell) = true)
    (hHH : adaptiveCoverCheck depth (childHH cell) = true) :
    adaptiveCoverCheck (depth + 1) cell = true := by
  by_cases hirr : physicallyIrrelevant cell = true
  · simp [adaptiveCoverCheck, hirr]
  by_cases hlocal : cellInsideLocal cell = true
  · simp [adaptiveCoverCheck, hirr, hlocal]
  by_cases hrejected : cell.rejected = true
  · simp [adaptiveCoverCheck, hirr, hlocal, hrejected]
  simp [adaptiveCoverCheck, hirr, hlocal, hrejected, hLL, hLH, hHL, hHH]

end PartE
end GerverSofa
