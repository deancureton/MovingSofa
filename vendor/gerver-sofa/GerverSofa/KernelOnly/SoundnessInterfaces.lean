import GerverSofa.ExactReplay
import GerverSofa.KernelOnly.Coordinates
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Semantic interfaces for the executable interval certificate

These definitions state, without hiding any mathematical assumption, the
bridges that turn the frozen rational replay into facts about `Real.sin`,
`Real.cos`, the two real systems, and their Jacobians.  Concrete proof terms
for these interfaces are the remaining analytic part of the end-to-end
certificate; no axiom is declared here.
-/

noncomputable section

namespace GerverSofa

open RatInterval

/-- A rational interval list encloses a finite real vector coordinatewise. -/
def EnclosesVec {n : Nat} (box : List RatInterval) (x : Vec n) : Prop :=
  box.length = n ∧
    ∀ i : Fin n, Contains (box.getD i.1 (point 0)) (x i)

/-- A one-dimensional real derivative certificate in the classical
difference-quotient form.  This is the exact real specialization of the
right-hand side of Mathlib's `hasDerivAt_iff_tendsto_slope_zero`: it states
that `(f (x+t)-f x)/t` tends to `f'` as `t → 0`, `t ≠ 0`.

Unlike storing raw `HasDerivAt`/`DifferentiableAt`, this proposition contains
no hidden `AddCommGroup`/`Module` instance path for the codomain `ℝ`; this
removes the instance diamond exposed by Lean 4.33 while retaining the full
mathematical meaning of an actual derivative. -/
def RealDerivativeAt (f : ℝ → ℝ) (f' x : ℝ) : Prop :=
  Filter.Tendsto
    (fun t : ℝ => t⁻¹ * (f (x + t) - f x))
    (nhdsWithin 0 (({0} : Set ℝ)ᶜ))
    (nhds f')

/-- Exact analytic correctness required from the executable trigonometric
layer.  The domain is the physical range used by the Gerver certificate. -/
structure TranscendentalSoundness : Prop where
  pi_mem : Contains ExactReplay.declaredPiInterval Real.pi
  sine_mem : ∀ (z : RatInterval) (x : ℝ),
    Contains z x → 0 ≤ x → x ≤ Real.pi / 2 →
      Contains (ExactReplay.sineInterval z) (Real.sin x)
  cosine_mem : ∀ (z : RatInterval) (x : ℝ),
    Contains z x → 0 ≤ x → x ≤ Real.pi / 2 →
      Contains (ExactReplay.cosineInterval z) (Real.cos x)

end GerverSofa
