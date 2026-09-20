import MovingSofa.Sofa.Maximum

/-!
# The paper's upper bound transported to the canonical target

The paper's main theorem bounds the real area of every moving sofa in the paper normalization by
the area of the paper Gerver sofa. The canonical and paper Gerver sets coincide, every admissible
set is a paper moving sofa, and admissible sets are compact, so the comparison of real areas is a
comparison of Lebesgue measures. No classical proposition is used.
-/

noncomputable section

namespace MovingSofa

open MeasureTheory
open scoped unitInterval

/-- Every admissible set has Lebesgue measure at most that of Gerver's sofa. -/
theorem areaUpperBound : AreaUpperBound := by
  intro s m hs
  have harea := paperGerverSofa_maximum.2 s (canonical_paper_motion_bridge.2 s m hs)
  rw [← gerver_canonical_paper_literal.1] at harea
  obtain ⟨-, hmeasS, hfinS⟩ := canonical_motion_compactness s m hs
  obtain ⟨mG, hmG⟩ := isMovingSofa_gerversSofa
  obtain ⟨-, hmeasG, hfinG⟩ := canonical_motion_compactness gerversSofa mG hmG
  exact (real_area_le_iff_volume_le s gerversSofa hmeasS hmeasG hfinS hfinG).mp harea

end MovingSofa
