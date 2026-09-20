import MovingSofa.Cap.BalancedExistence
import MovingSofa.Cap.Monotone
import MovingSofa.Motion.Monotonization

noncomputable section

namespace MovingSofa

def IsBalancedMaximumSofa (s : Set Point) (ω : ℝ) : Prop :=
  (∃ s₀ : Set Point, IsStandardPosition s₀ ω ∧ s = monotonization s₀ ω) ∧
    ∃ K : CapSpace ω, (K.val : Set Point) = capOfSofa s ω ∧ IsBalancedMaximumCap K

theorem exists_balancedMaximumSofa (ω : ℝ) (hω : 0 < ω)
    (hω' : ω ≤ Real.pi / 2) :
    ∃ K : CapSpace ω, IsBalancedMaximumCap K ∧
      IsBalancedMaximumSofa ((K.val : Set Point) \ capNiche K) ω ∧
      ∀ s : Set Point, HasRotationAngle s ω →
        ClassicalResults.area s ≤ ClassicalResults.area ((K.val : Set Point) \ capNiche K) := by
  obtain ⟨K, hK⟩ := exists_balancedMaximumCap ω hω hω'
  obtain ⟨s₀, hs₀, hcap⟩ := (cap_isMonotoneCap_iff_niche_subset K).mpr
    (balancedMaximumCap_niche_subset K hK)
  have hshape := monotoneSofa_structure (monotonization s₀ ω) ω ⟨s₀, hs₀, rfl⟩ K hcap
  have hmonoS : ∃ s₀ : Set Point, IsStandardPosition s₀ ω ∧
      (K.val : Set Point) \ capNiche K = monotonization s₀ ω := ⟨s₀, hs₀, hshape.symm⟩
  have hcapS : (K.val : Set Point) = capOfSofa ((K.val : Set Point) \ capNiche K) ω := by
    rwa [← hshape]
  have hareaK := capAreaFunctional_eq_sofaArea _ ω hmonoS K hcapS
  refine ⟨K, hK, ⟨hmonoS, K, hcapS, hK⟩, ?_⟩
  intro s hs
  obtain ⟨v, hv⟩ := (exists_standardPosition_translation s ω hs ⟨hω, hω'⟩).1
  let s₁ := (fun p ↦ p + v) '' s
  have hstd := standardPosition_monotonization_standard s₁ ω hv
  obtain ⟨L, hL⟩ := standardPosition_cap (monotonization s₁ ω) ω hstd.1
  calc
    ClassicalResults.area s = ClassicalResults.area s₁ :=
      (ClassicalResults.area_image_add s v).symm
    _ ≤ ClassicalResults.area (monotonization s₁ ω) :=
      MeasureTheory.measureReal_mono hstd.2 hstd.1.1.measure_lt_top.ne
    _ = capAreaFunctional L :=
      (capAreaFunctional_eq_sofaArea _ ω ⟨s₁, hv, rfl⟩ L hL).symm
    _ ≤ capAreaFunctional K := balancedMaximumCap_maximizes_area K hK L
    _ = _ := hareaK

end MovingSofa
