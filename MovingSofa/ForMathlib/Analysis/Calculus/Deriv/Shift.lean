import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Shifting the base point of a derivative

`HasDerivAt.comp_add_const` transports a derivative at a shifted base point to the shifted
function; this file records the converse implication, packaged as an `Iff`.
-/

/-- A derivative at a shifted base point is the derivative of the shifted function. -/
theorem hasDerivAt_comp_add_const_iff {𝕜 : Type*} [NontriviallyNormedField 𝕜] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : 𝕜 → F} {f' : F} (x a : 𝕜) :
    HasDerivAt (fun u ↦ f (u + a)) f' x ↔ HasDerivAt f f' (x + a) := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.comp_add_const x a⟩
  have h' : HasDerivAt (fun u ↦ f (u + a)) f' (x + a + -a) := by simpa using h
  simpa using h'.comp_add_const (x + a) (-a)
