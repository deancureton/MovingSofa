import MovingSofa.Curve.SmoothIntervalPaths
import MovingSofa.Cap.Tail.Space

noncomputable section

namespace MovingSofa

def capCornerBV (K : SpecialCapSpace) {a b : ℝ}
    (h : Set.Icc a b ⊆ Set.Icc 0 (Real.pi / 2)) : ContinuousBVPaths a b :=
  continuousBVOfContDiffOn (capInnerCorner K.val) (K.property.1.2.1.mono h)

def capMiddleBV (K : SpecialCapSpace) :
    ContinuousBVPaths paperGerverConstants.2.1 paperGerverConstants.2.2 :=
  capCornerBV K (by
    have hφ : 0 ≤ GerversSofa.φ := GerversSofa.ABφθSpec.existsUnique.choose_spec.1.1
    intro t ht
    change GerversSofa.φ ≤ t ∧ t ≤ Real.pi / 2 - GerversSofa.φ at ht
    exact ⟨le_trans hφ ht.1, by linarith [ht.2]⟩)

end MovingSofa
