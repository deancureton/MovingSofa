import Mathlib.Analysis.Normed.Affine.ContinuousAffineMap
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

namespace ContinuousAffineMap

variable {E F G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup G] [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G]

/-- Precomposition by a fixed continuous affine map is continuous. -/
theorem continuous_comp_right (g : E →ᴬ[ℝ] F) :
    Continuous (fun f : F →ᴬ[ℝ] G ↦ f.comp g) := by
  let C : NNReal := ⟨‖g‖ + 1, by positivity⟩
  apply (LipschitzWith.of_dist_le_mul (K := C) fun f h ↦ ?_).continuous
  rw [dist_eq_norm, dist_eq_norm]
  have heq : f.comp g - h.comp g = (f - h).comp g := by
    ext x
    simp
  rw [heq]
  calc
    ‖(f - h).comp g‖ ≤ ‖f - h‖ * ‖g‖ + ‖(f - h) 0‖ :=
      ContinuousAffineMap.norm_comp_le _ _
    _ ≤ ‖f - h‖ * ‖g‖ + ‖f - h‖ := by
      gcongr
      exact ContinuousAffineMap.norm_image_zero_le _
    _ = (C : ℝ) * ‖f - h‖ := by
      change _ = (‖g‖ + 1) * ‖f - h‖
      ring

end ContinuousAffineMap
