import MovingSofa.Geometry.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

noncomputable section

open scoped unitInterval

universe u v w

namespace MovingSofa

/-- A barycentric operation has an injective realization as convex combinations in a real space. -/
def IsConvexDomain {α : Type u} (c : I → α → α → α) : Prop :=
  ∃ (V : ModuleCat.{v} ℝ) (e : α → V), Function.Injective e ∧
    Convex ℝ (Set.range e) ∧
    ∀ (t : I) x y, e (c t x y) = (1 - (t : ℝ)) • e x + (t : ℝ) • e y

/-- Preservation of the specified barycentric operations. -/
def IsConvexLinear {α : Type u} {β : Type v}
    (cα : I → α → α → α) (cβ : I → β → β → β) (f : α → β) : Prop :=
  ∀ t x y, f (cα t x y) = cβ t (f x) (f y)

/-- Separate preservation of barycentric combinations in both variables. -/
def IsConvexBilinear {α : Type u} {β : Type v} {γ : Type w}
    (cα : I → α → α → α) (cβ : I → β → β → β) (cγ : I → γ → γ → γ)
    (g : α → β → γ) : Prop :=
  (∀ x, IsConvexLinear cβ cγ (g x)) ∧
    ∀ y, IsConvexLinear cα cγ (fun x ↦ g x y)

/-- The usual barycentric combination of real numbers. -/
def realCombination (t : I) (x y : ℝ) : ℝ := (1 - (t : ℝ)) * x + (t : ℝ) * y

/-- A quadratic functional is the diagonal of a separately convex-linear real map. -/
def IsQuadraticFunctional {α : Type u} (c : I → α → α → α) (f : α → ℝ) : Prop :=
  ∃ g : α → α → ℝ, IsConvexBilinear c c realCombination g ∧ ∀ x, f x = g x x

/-- Concavity or convexity according to the direction of the barycentric inequality. -/
def IsConvexFunctional {α : Type u} (c : I → α → α → α) (f : α → ℝ)
    (concave : Bool) : Prop :=
  ∀ t x y, if concave then realCombination t (f x) (f y) ≤ f (c t x y)
    else f (c t x y) ≤ realCombination t (f x) (f y)

/-- The segment function, extended by zero outside its parameter interval. -/
def segmentFunctional {α : Type u} (c : I → α → α → α) (f : α → ℝ)
    (x y : α) (t : ℝ) : ℝ :=
  if ht : t ∈ Set.Icc (0 : ℝ) 1 then f (c ⟨t, ht⟩ x y) else 0

/-- The right derivative along the barycentric segment; used for quadratic functionals. -/
def convexDirectionalDerivative {α : Type u} (c : I → α → α → α)
    (f : α → ℝ) (x y : α) : ℝ :=
  derivWithin (segmentFunctional c f x y) (Set.Icc 0 1) 0

/-- Minkowski interpolation of nonempty compact convex bodies, including both endpoints. -/
def convexBodyCombination (t : I) (K L : ConvexBody Point) : ConvexBody Point :=
  (1 - (t : ℝ)) • K + (t : ℝ) • L


end MovingSofa
