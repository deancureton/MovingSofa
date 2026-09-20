import GerverSofa.KernelOnly.PartE.E24AlignedRegionFoundation

/-!
# E24 aligned-region semantic closure

This file contains no closed heavy computation.  It proves that the four
aligned rectangles cover the complement of the E21 local cell inside the
physical triangle and turns four Boolean adaptive-cover certificates into the
terminal DeepMind-shaped uniqueness theorem.
-/

noncomputable section

namespace GerverSofa
namespace PartE

open LeanCert.Core

theorem e24AlignedRoots_cover_outside_local
    (phi theta : ℝ)
    (hdom : PhysicalAngleDomain phi theta)
    (houtside : ¬ localAngleCell.Contains phi theta) :
    e24PhiBelowRoot.Contains phi theta ∨
      e24PhiAboveRoot.Contains phi theta ∨
      e24ThetaBelowRoot.Contains phi theta ∨
      e24ThetaAboveRoot.Contains phi theta := by
  have hglobal :=
    physicalAngleDomain_mem_globalAngleRoot phi theta hdom
  change
    phi ∈ globalAngleRoot.phiI ∧ theta ∈ globalAngleRoot.thetaI at hglobal
  simp only [globalAngleRoot, IntervalRat.mem_def] at hglobal

  by_cases hpLo :
      phi ≤ (((391 / 10000 : ℚ) : ℝ))
  · left
    change
      phi ∈ e24PhiBelowRoot.phiI ∧ theta ∈ e24PhiBelowRoot.thetaI
    simp only [e24PhiBelowRoot, IntervalRat.mem_def]
    exact ⟨⟨hglobal.1.1, hpLo⟩, hglobal.2⟩

  by_cases hpHi :
      (((157 / 4000 : ℚ) : ℝ)) ≤ phi
  · right; left
    change
      phi ∈ e24PhiAboveRoot.phiI ∧ theta ∈ e24PhiAboveRoot.thetaI
    simp only [e24PhiAboveRoot, IntervalRat.mem_def]
    exact ⟨⟨hpHi, hglobal.1.2⟩, hglobal.2⟩

  by_cases htLo :
      theta ≤ (((68113 / 100000 : ℚ) : ℝ))
  · right; right; left
    change
      phi ∈ e24ThetaBelowRoot.phiI ∧ theta ∈ e24ThetaBelowRoot.thetaI
    simp only [e24ThetaBelowRoot, IntervalRat.mem_def]
    exact ⟨hglobal.1, ⟨hglobal.2.1, htLo⟩⟩

  by_cases htHi :
      (((34069 / 50000 : ℚ) : ℝ)) ≤ theta
  · right; right; right
    change
      phi ∈ e24ThetaAboveRoot.phiI ∧ theta ∈ e24ThetaAboveRoot.thetaI
    simp only [e24ThetaAboveRoot, IntervalRat.mem_def]
    exact ⟨hglobal.1, ⟨htHi, hglobal.2.2⟩⟩

  have hphiLo :
      (((391 / 10000 : ℚ) : ℝ)) < phi :=
    lt_of_not_ge hpLo
  have hphiHi :
      phi < (((157 / 4000 : ℚ) : ℝ)) :=
    lt_of_not_ge hpHi
  have hthetaLo :
      (((68113 / 100000 : ℚ) : ℝ)) < theta :=
    lt_of_not_ge htLo
  have hthetaHi :
      theta < (((34069 / 50000 : ℚ) : ℝ)) :=
    lt_of_not_ge htHi

  exfalso
  apply houtside
  change
    phi ∈ localAngleCell.phiI ∧ theta ∈ localAngleCell.thetaI
  constructor
  · change phi ∈ localAngleX (0 : Fin 2)
    simp only [localAngleX, IntervalRat.mem_def]
    exact ⟨hphiLo.le, hphiHi.le⟩
  · change theta ∈ localAngleX (1 : Fin 2)
    simp only [localAngleX, IntervalRat.mem_def]
    exact ⟨hthetaLo.le, hthetaHi.le⟩

theorem e24NoCommonZeroOutsideLocal_of_alignedChecks
    (hPhiBelow : adaptiveCoverCheck 14 e24PhiBelowRoot = true)
    (hPhiAbove : adaptiveCoverCheck 16 e24PhiAboveRoot = true)
    (hThetaBelow : adaptiveCoverCheck 18 e24ThetaBelowRoot = true)
    (hThetaAbove : adaptiveCoverCheck 19 e24ThetaAboveRoot = true)
    (phi theta : ℝ)
    (hdom : PhysicalAngleDomain phi theta)
    (houtside : ¬ localAngleCell.Contains phi theta) :
    ¬ (scaledResidualOne phi theta = 0 ∧
      scaledResidualTwo phi theta = 0) := by
  rcases e24AlignedRoots_cover_outside_local phi theta hdom houtside with
    hmem | hmem | hmem | hmem
  · exact adaptiveCoverCheck_no_common_zero
      14 e24PhiBelowRoot hPhiBelow phi theta hdom hmem houtside
  · exact adaptiveCoverCheck_no_common_zero
      16 e24PhiAboveRoot hPhiAbove phi theta hdom hmem houtside
  · exact adaptiveCoverCheck_no_common_zero
      18 e24ThetaBelowRoot hThetaBelow phi theta hdom hmem houtside
  · exact adaptiveCoverCheck_no_common_zero
      19 e24ThetaAboveRoot hThetaAbove phi theta hdom hmem houtside

theorem e24ScaledResidualEnclosureTarget_of_alignedChecks
    (hPhiBelow : adaptiveCoverCheck 14 e24PhiBelowRoot = true)
    (hPhiAbove : adaptiveCoverCheck 16 e24PhiAboveRoot = true)
    (hThetaBelow : adaptiveCoverCheck 18 e24ThetaBelowRoot = true)
    (hThetaAbove : adaptiveCoverCheck 19 e24ThetaAboveRoot = true) :
    ScaledResidualEnclosureTarget := by
  intro phi theta hspec
  by_cases hin : localAngleCell.Contains phi theta
  · exact wideLocalReconstructionEnclosureTarget phi theta hspec hin
  · have hnozero :=
      e24NoCommonZeroOutsideLocal_of_alignedChecks
        hPhiBelow hPhiAbove hThetaBelow hThetaAbove
        phi theta hspec.1 hin
    exact (hnozero ⟨hspec.2.2.2.2.1, hspec.2.2.2.2.2⟩).elim

theorem deepMindABPhiTheta_existsUnique_of_alignedChecks
    (hPhiBelow : adaptiveCoverCheck 14 e24PhiBelowRoot = true)
    (hPhiAbove : adaptiveCoverCheck 16 e24PhiAboveRoot = true)
    (hThetaBelow : adaptiveCoverCheck 18 e24ThetaBelowRoot = true)
    (hThetaAbove : adaptiveCoverCheck 19 e24ThetaAboveRoot = true) :
    ∃! ABphiTheta : ℝ × ℝ × ℝ × ℝ,
      DeepMindABPhiThetaSpec
        ABphiTheta.1 ABphiTheta.2.1 ABphiTheta.2.2.1 ABphiTheta.2.2.2 :=
  deepMindABPhiTheta_existsUnique_of_twoAngleEnclosure
    ((scaledResidualEnclosureTarget_iff_twoAngleEnclosureTarget).1
      (e24ScaledResidualEnclosureTarget_of_alignedChecks
        hPhiBelow hPhiAbove hThetaBelow hThetaAbove))

end PartE
end GerverSofa
