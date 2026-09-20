import MovingSofa.Convex.Combination

noncomputable section

open scoped unitInterval

universe u

namespace MovingSofa

def EquivalentModuloConvexLinear {α : Type u} (c : I → α → α → α)
    (f g : α → ℝ) : Prop :=
  IsConvexLinear c realCombination (fun x ↦ f x - g x)

end MovingSofa
