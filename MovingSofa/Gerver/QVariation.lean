import MovingSofa.Gerver.PhaseIntegration

/-!
# The variation of `𝒬` at Gerver's cap is nonpositive

At the Gerver base triple the tail geometry identifies the two tail endpoints with the two cap
corners, so `upperBoundQ_variation` presents the derivative as `qVariationIntegral`.  Two of its
four integration windows are larger than the two active tail windows, and the excess is null:
on `(φᴿ, π/2 - θ)` one and the same contact point supports the right tail at both endpoint
normals, and likewise for the left tail on `(π/2 + θ, π/2 + φᴸ)`, so
`oppositeSurfaceData_angleImage_Ioo_eq_zero_of_mem_exposedEdge` applies.

The variation integral is therefore the sum of the eight phase contributions
(`qVariationIntegral_eq_phaseSum`), and each of them is nonpositive
(`gerverPhaseContribution_nonpos`) because the tail support sums are exactly `1` on the two active
windows while the competitor's are at most `1`.
-/

noncomputable section

open MeasureTheory

namespace MovingSofa

theorem gerver_upperBoundQ_variation (X Y : CapTailSpace)
    (hK : (X.cap.val.val : Set Point) = capOfSofa paperGerverSofa (Real.pi / 2))
    (hB : (X.rightBody : Set Point) = (canonicalTailSets X.cap).1)
    (hD : (X.leftBody : Set Point) = (canonicalTailSets X.cap).2) :
    convexDirectionalDerivative capTailCombination upperBoundQ X Y ≤ 0 := by
  have horder := gerverStageTimes_strictMono
  have h01 := horder (show (0 : Fin 6) < 1 by decide)
  have h02 := horder (show (0 : Fin 6) < 2 by decide)
  have h13 := horder (show (1 : Fin 6) < 3 by decide)
  have h24 := horder (show (2 : Fin 6) < 4 by decide)
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hr : paperGerverConstants.2.1 = GerversSofa.φ := rfl
  have ht2 : gerverStageTimes 2 = GerversSofa.θ := by simp [gerverStageTimes]
  have ht3 : gerverStageTimes 3 = Real.pi / 2 - GerversSofa.θ := by simp [gerverStageTimes]
  simp only [gerverStageTimes, Matrix.cons_val] at h01 h02 h13 h24
  obtain ⟨-, -, hLcorner, hLend, hDvert, -, hRcorner, hRstart, hBvert, -, hsumD, hsumB⟩ :=
    gerver_tailGeometry X.cap X.rightBody X.leftBody hK hB hD
  -- ### The general variation formula applies at this base triple
  rw [upperBoundQ_variation X Y (hRstart.trans hRcorner.symm) (hLend.trans hLcorner.symm)]
  -- ### The right tail carries no surface measure between its two active windows
  have hinactiveB : (oppositeSurfaceData X.rightBody).1 ((fun s : ℝ ↦ (s : Real.Angle)) ''
      Set.Ioo paperGerverConstants.2.1 (Real.pi / 2 - GerversSofa.θ)) = 0 := by
    refine oppositeSurfaceData_angleImage_Ioo_eq_zero_of_mem_exposedEdge X.rightBody
      (p := paperGerverContacts (gerverStageTimes 3) 1) h13 (by rw [hr]; linarith) ?_ ?_
    · have h : paperGerverContacts (gerverStageTimes 3) 1 =
          (edgeVertices X.rightBody
            ((Real.pi + paperGerverConstants.2.1 : ℝ) : Real.Angle)).1 := hRstart.symm
      rw [h, show ((paperGerverConstants.2.1 + Real.pi : ℝ) : Real.Angle) =
        ((Real.pi + paperGerverConstants.2.1 : ℝ) : Real.Angle) from by congr 1; ring]
      exact edgeVertices_fst_mem _ _
    · have h : paperGerverContacts (gerverStageTimes 3) 1 =
          (edgeVertices X.rightBody
            ((Real.pi + gerverStageTimes 3 : ℝ) : Real.Angle)).2 := by rw [hBvert]
      rw [h, show ((Real.pi / 2 - GerversSofa.θ + Real.pi : ℝ) : Real.Angle) =
        ((Real.pi + gerverStageTimes 3 : ℝ) : Real.Angle) from by rw [ht3]; congr 1; ring]
      exact edgeVertices_snd_mem _ _
  -- ### The left tail carries no surface measure between its two active windows
  have hinactiveD : (oppositeSurfaceData X.leftBody).1 ((fun s : ℝ ↦ (s : Real.Angle)) ''
      Set.Ioo (Real.pi / 2 + GerversSofa.θ)
        (Real.pi / 2 + paperGerverConstants.2.2)) = 0 := by
    have hlt : Real.pi / 2 + GerversSofa.θ < Real.pi / 2 + paperGerverConstants.2.2 := by
      change Real.pi / 2 + GerversSofa.θ < Real.pi / 2 + (Real.pi / 2 - GerversSofa.φ)
      linarith
    refine oppositeSurfaceData_angleImage_Ioo_eq_zero_of_mem_exposedEdge X.leftBody
      (p := paperGerverContacts (gerverStageTimes 2) 3) hlt (by
        change Real.pi / 2 + (Real.pi / 2 - GerversSofa.φ) <
          Real.pi / 2 + GerversSofa.θ + Real.pi
        linarith) ?_ ?_
    · have h : paperGerverContacts (gerverStageTimes 2) 3 =
          (edgeVertices X.leftBody
            ((3 * Real.pi / 2 + gerverStageTimes 2 : ℝ) : Real.Angle)).1 := by rw [hDvert]
      rw [h, show ((Real.pi / 2 + GerversSofa.θ + Real.pi : ℝ) : Real.Angle) =
        ((3 * Real.pi / 2 + gerverStageTimes 2 : ℝ) : Real.Angle) from by
          rw [ht2]; congr 1; ring]
      exact edgeVertices_fst_mem _ _
    · have h : paperGerverContacts (gerverStageTimes 2) 3 =
          (edgeVertices X.leftBody
            ((3 * Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle)).2 := hLend.symm
      rw [h, show ((Real.pi / 2 + paperGerverConstants.2.2 + Real.pi : ℝ) : Real.Angle) =
        ((3 * Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle) from by congr 1; ring]
      exact edgeVertices_snd_mem _ _
  -- ### On the two active windows the base support sums are exactly one
  have hbaseB : ∀ t ∈ gerverPhaseAngles 3 ∪ gerverPhaseAngles 4,
      supportValue X.cap.val.val t + (oppositeSurfaceData X.rightBody).2 t = 1 := by
    intro t ht
    rw [gerverPhaseAngles_three_union_four] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    have h := hsumB s (by rw [ht3]; exact ⟨hs.1, hs.2.le⟩)
    simp only [oppositeSurfaceData]
    rw [show ((s : Real.Angle) + ((Real.pi : ℝ) : Real.Angle)) =
      ((Real.pi + s : ℝ) : Real.Angle) from by rw [← Real.Angle.coe_add]; congr 1; ring]
    exact h
  have hbaseD : ∀ t ∈ gerverPhaseAngles 5 ∪ gerverPhaseAngles 6,
      supportValue X.cap.val.val t + (oppositeSurfaceData X.leftBody).2 t = 1 := by
    intro t ht
    rw [gerverPhaseAngles_five_union_six] at ht
    obtain ⟨u, hu, rfl⟩ := ht
    have h := hsumD (u - Real.pi / 2) (by
      rw [gerverStageTimes_zero, ht2]
      exact ⟨by linarith [hu.1], by linarith [hu.2]⟩)
    rw [show ((Real.pi / 2 + (u - Real.pi / 2) : ℝ) : Real.Angle) = (u : Real.Angle) from by
      congr 1; ring] at h
    simp only [oppositeSurfaceData]
    rw [show ((u : Real.Angle) + ((Real.pi : ℝ) : Real.Angle)) =
      ((3 * Real.pi / 2 + (u - Real.pi / 2) : ℝ) : Real.Angle) from by
      rw [← Real.Angle.coe_add]; congr 1; ring]
    exact h
  -- ### Each of the eight phase contributions is nonpositive
  rw [qVariationIntegral_eq_phaseSum X Y hinactiveB hinactiveD]
  exact Finset.sum_nonpos fun i _ ↦ gerverPhaseContribution_nonpos X Y
    (gerver_phaseMeasures X.cap X.rightBody X.leftBody hK hB hD) hbaseB hbaseD i

end MovingSofa
