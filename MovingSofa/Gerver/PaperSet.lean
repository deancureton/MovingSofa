import MovingSofa.Gerver.PaperPath

noncomputable section

namespace MovingSofa

/-- Gerver's paper-frame set, cut out by the explicit path of rotated hallways. -/
def paperGerverSofa : Set Point :=
  (strips (Real.pi / 2)).1 ∩ (strips (Real.pi / 2)).2.2 ∩
    ⋂ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      (fun p ↦ rotationMap (t : Real.Angle) p + paperGerverPath t) '' hallway

end MovingSofa
