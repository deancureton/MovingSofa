import MovingSofa.Convex.Combination

/-!
# Pulling barycentric functionals back along convex-linear maps

A convex-linear map transports one barycentric operation to another, so every notion defined
from that operation pulls back along it: a quadratic functional stays quadratic, and its
directional derivative along a segment is the directional derivative between the images of the
two endpoints. Neither statement needs any topology or differentiability: the two segment
functions are literally equal.
-/

noncomputable section

open scoped unitInterval

universe u v

namespace MovingSofa

/-- A quadratic functional pulled back along a convex-linear map is quadratic. -/
theorem IsQuadraticFunctional.comp_isConvexLinear {α : Type u} {β : Type v}
    {cα : I → α → α → α} {cβ : I → β → β → β} {F : α → β}
    (hF : IsConvexLinear cα cβ F) {f : β → ℝ} (hf : IsQuadraticFunctional cβ f) :
    IsQuadraticFunctional cα fun x ↦ f (F x) := by
  obtain ⟨g, hg, hfg⟩ := hf
  refine ⟨fun x y ↦ g (F x) (F y), ⟨fun x s y z ↦ ?_, fun y s x z ↦ ?_⟩, fun x ↦ hfg (F x)⟩
  · show g (F x) (F (cα s y z)) = _
    rw [hF]
    exact hg.1 (F x) s (F y) (F z)
  · show g (F (cα s x z)) (F y) = _
    rw [hF]
    exact hg.2 (F y) s (F x) (F z)

/-- The directional derivative of a functional pulled back along a convex-linear map is the
directional derivative of the functional between the images. -/
theorem convexDirectionalDerivative_comp_isConvexLinear {α : Type u} {β : Type v}
    {cα : I → α → α → α} {cβ : I → β → β → β} {F : α → β}
    (hF : IsConvexLinear cα cβ F) (f : β → ℝ) (x y : α) :
    convexDirectionalDerivative cα (fun z ↦ f (F z)) x y =
      convexDirectionalDerivative cβ f (F x) (F y) := by
  unfold convexDirectionalDerivative
  congr 1
  funext s
  simp only [segmentFunctional]
  split_ifs with hs
  · exact congrArg f (hF _ x y)
  · rfl

/-- A convex or concave functional pulled back along a convex-linear map keeps its direction of
convexity. -/
theorem IsConvexFunctional.comp_isConvexLinear {α : Type u} {β : Type v}
    {cα : I → α → α → α} {cβ : I → β → β → β} {F : α → β}
    (hF : IsConvexLinear cα cβ F) {f : β → ℝ} {concave : Bool}
    (hf : IsConvexFunctional cβ f concave) :
    IsConvexFunctional cα (fun x ↦ f (F x)) concave := by
  intro s x y
  have h := hf s (F x) (F y)
  rw [← hF s x y] at h
  exact h

end MovingSofa
