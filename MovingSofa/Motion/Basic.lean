import MovingSofa.Geometry.Hallway
import MovingSofa.Cap.Basic

noncomputable section

open scoped unitInterval

namespace MovingSofa

/-- A paper motion permits an initial translation and preserves orientation at every time. -/
def IsPaperMotion (s : Set Point) (m : I → Point ≃ᵃⁱ[ℝ] Point) : Prop :=
  IsConnected s ∧ IsClosed s ∧ Continuous m ∧
    (∃ q : Point, ∀ p, m 0 p = p + q) ∧
    (∀ t, ∃ a : Real.Angle, ∀ p, m t p = rotationMap a p + m t 0) ∧
    m 0 '' s ⊆ horizontalHallway ∧
    (∀ t, m t '' s ⊆ hallway) ∧ m 1 '' s ⊆ verticalHallway

/-- Movability in the paper's translation-invariant convention. -/
def IsPaperMovingSofa (s : Set Point) : Prop :=
  ∃ m, IsPaperMotion s m

/-- Clockwise rotation angle of a particular admissible lifted motion witness. -/
def HasRotationAngle (s : Set Point) (ω : ℝ) : Prop :=
  ∃ (m : I → Point ≃ᵃⁱ[ℝ] Point), IsPaperMotion s m ∧
    ∃ α : I → ℝ, Continuous α ∧ α 0 = 0 ∧ α 1 = -ω ∧
      ∀ t p, m t p = rotationMap (α t : Real.Angle) p + m t 0

/-- Standard position for a compact moving sofa with the specified rotation angle. -/
def IsStandardPosition (s : Set Point) (ω : ℝ) : Prop :=
  IsCompact s ∧ HasRotationAngle s ω ∧ 0 < ω ∧ ω ≤ Real.pi / 2 ∧
    supportValue s (ω : Real.Angle) = 1 ∧
    supportValue s ((Real.pi / 2 : ℝ) : Real.Angle) = 1

/-- The cap set constructed from all supporting outer quadrants. -/
def capOfSofa (s : Set Point) (ω : ℝ) : Set Point :=
  (stripParallelogram ω).1 ∩
    ⋂ t ∈ Set.Icc 0 ω, (rotatingHallwayParts s (t : Real.Angle)).outerQuadrant

/-- The intersection of supporting hallways used for monotonization. -/
def monotonization (s : Set Point) (ω : ℝ) : Set Point :=
  (stripParallelogram ω).1 ∩ ⋂ t ∈ Set.Icc 0 ω, supportingHallway s (t : Real.Angle)

/-- A monotone sofa is the monotonization of a sofa in standard position. -/
def IsMonotoneSofa (s : Set Point) : Prop :=
  ∃ (s₀ : Set Point) (ω : ℝ), IsStandardPosition s₀ ω ∧ s = monotonization s₀ ω

/-- The finite-angle outer approximation to a cap. -/
def angleCap (Θ : AngleSet) (K : CapSpace Θ.angle) : Set Point :=
  (stripParallelogram Θ.angle).1 ∩
    ⋂ t ∈ Θ.directions, (rotatingHallwayParts (K.1 : Set Point) (t : Real.Angle)).outerQuadrant

end MovingSofa
