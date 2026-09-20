import MovingSofa.Gerver.ParameterDictionary

noncomputable section

namespace MovingSofa

theorem gerver_reverse_physical_domain (p : GerverSofa.Romik.Params)
    (hp : p ∈ gerverDirectBox) :
    0 < (gerverParameterDictionary.2 p).phi ∧
    (gerverParameterDictionary.2 p).phi < (gerverParameterDictionary.2 p).theta ∧
    (gerverParameterDictionary.2 p).theta < Real.pi / 4 ∧
    0 < (gerverParameterDictionary.2 p).a ∧ 0 < (gerverParameterDictionary.2 p).b ∧
    (39 : ℝ) / 1000 ≤ (gerverParameterDictionary.2 p).phi ∧
    (gerverParameterDictionary.2 p).phi ≤ (40 : ℝ) / 1000 := by
  dsimp [gerverDirectBox, GerverSofa.Romik.box, GerverSofa.qR] at hp
  rcases hp with ⟨_, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _,
    hb1lo, hb1hi, hb2lo, _, _, _, _, _,
    _, _, _, _, _, _, _, _,
    hphilo, hphihi, hthetalo, hthetahi⟩
  norm_num at hb1lo hb1hi hb2lo hphilo hphihi hthetalo hthetahi
  have hphiLo : (39 : ℝ) / 1000 ≤ p.phi := by linarith only [hphilo]
  have hphiHi : p.phi ≤ (1 : ℝ) / 25 := by linarith only [hphihi]
  have hphiPos : (0 : ℝ) < p.phi := by linarith only [hphiLo]
  have hthetaLo : (3 : ℝ) / 5 ≤ p.theta := by linarith only [hthetalo]
  have hthetaHi : p.theta ≤ (7 : ℝ) / 10 := by linarith only [hthetahi]
  have hb1Lo : (-66 : ℝ) / 125 ≤ p.b1 := by linarith only [hb1lo]
  have hb1Hi : p.b1 ≤ (-527 : ℝ) / 1000 := by linarith only [hb1hi]
  have hb2Lo : (23 : ℝ) / 25 ≤ p.b2 := by linarith only [hb2lo]
  have hAPos : (0 : ℝ) < p.phi - 1 - 2 * p.b1 := by linarith only [hphiLo, hb1Hi]
  have hBPos :
      (0 : ℝ) <
        p.b2 + 1 / 2 - (1 + (p.phi - 1 - 2 * p.b1)) * p.phi / 2 + p.phi ^ 2 / 4 := by
    have hprod : (0 : ℝ) ≤ (p.b1 + 66 / 125) * p.phi :=
      mul_nonneg (by linarith only [hb1Lo]) hphiPos.le
    have hsq : (0 : ℝ) ≤ p.phi * (1 / 25 - p.phi) :=
      mul_nonneg hphiPos.le (by linarith only [hphiHi])
    nlinarith only [hb2Lo, hprod, hsq, hphiPos, hphiHi]
  refine ⟨hphiPos, show p.phi < p.theta from ?_,
    show p.theta < Real.pi / 4 from ?_, hAPos, hBPos, hphiLo,
    show p.phi ≤ (40 : ℝ) / 1000 from ?_⟩
  · linarith only [hphiHi, hthetaLo]
  · nlinarith only [hthetaHi, Real.pi_gt_three]
  · linarith only [hphiHi]

end MovingSofa
