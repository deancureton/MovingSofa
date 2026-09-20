import MovingSofa.Motion.Basic
import MovingSofa.ForMathlib.Analysis.Normed.Affine.ContinuousAffineMap

noncomputable section

open scoped unitInterval

namespace MovingSofa

private def translatedMotion (v : Point) (m : I → Point ≃ᵃⁱ[ℝ] Point) (t : I) :
    Point ≃ᵃⁱ[ℝ] Point :=
  (AffineIsometryEquiv.vaddConst ℝ (-v)).trans (m t)

private theorem continuous_translatedMotion (v : Point)
    (m : I → Point ≃ᵃⁱ[ℝ] Point) (hm : Continuous m) :
    Continuous (translatedMotion v m) := by
  rw [continuous_induced_rng]
  have hmc : Continuous (fun t ↦ (m t).toAffineIsometry.toContinuousAffineMap) :=
    continuous_induced_dom.comp hm
  apply (ContinuousAffineMap.continuous_comp_right
    (AffineIsometryEquiv.vaddConst ℝ (-v)).toAffineIsometry.toContinuousAffineMap).comp
      hmc |>.congr
  intro t
  rfl

/-- Translating a sofa preserves each admitted rotation angle. -/
theorem hasRotationAngle_image_add (s : Set Point) (v : Point) (ω : ℝ)
    (hs : HasRotationAngle s ω) :
    HasRotationAngle ((fun p ↦ p + v) '' s) ω := by
  obtain ⟨m, hm, α, hα, hα0, hα1, hmotion⟩ := hs
  refine ⟨translatedMotion v m, ?_, α, hα, hα0, hα1, ?_⟩
  · obtain ⟨hconn, hclosed, hcont, ⟨q, hq⟩, hrot, hini, hall, hfinal⟩ := hm
    refine ⟨hconn.image _ (by fun_prop), ?_, continuous_translatedMotion v m hcont,
      ⟨q - v, ?_⟩, ?_, ?_, ?_, ?_⟩
    · change IsClosed ((AffineIsometryEquiv.vaddConst ℝ v) '' s)
      exact (AffineIsometryEquiv.vaddConst ℝ v).toHomeomorph.isClosedMap s hclosed
    · intro p
      change m 0 (p - v) = p + (q - v)
      rw [hq]
      abel
    · intro t
      obtain ⟨a, ha⟩ := hrot t
      refine ⟨a, fun p ↦ ?_⟩
      change m t ((AffineIsometryEquiv.vaddConst ℝ (-v)) p) =
        rotationMap a p + m t ((AffineIsometryEquiv.vaddConst ℝ (-v)) 0)
      rw [ha ((AffineIsometryEquiv.vaddConst ℝ (-v)) p),
        ha ((AffineIsometryEquiv.vaddConst ℝ (-v)) 0)]
      have hvp : (AffineIsometryEquiv.vaddConst ℝ (-v)) p = p - v := by rfl
      have hv0 : (AffineIsometryEquiv.vaddConst ℝ (-v)) 0 = -v := by simp
      rw [hvp, hv0]
      simp only [rotationMap, map_sub, map_neg]
      abel
    · rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact hini ⟨y, hy, by simp [translatedMotion]⟩
    · intro t
      rintro _ ⟨x, ⟨y, hy, rfl⟩, rfl⟩
      exact hall t ⟨y, hy, by simp [translatedMotion]⟩
    · rintro _ ⟨x, ⟨y, hy, rfl⟩, rfl⟩
      exact hfinal ⟨y, hy, by simp [translatedMotion]⟩
  · intro t p
    change m t ((AffineIsometryEquiv.vaddConst ℝ (-v)) p) =
      rotationMap (α t : Real.Angle) p +
        m t ((AffineIsometryEquiv.vaddConst ℝ (-v)) 0)
    rw [hmotion t ((AffineIsometryEquiv.vaddConst ℝ (-v)) p),
      hmotion t ((AffineIsometryEquiv.vaddConst ℝ (-v)) 0)]
    have hvp : (AffineIsometryEquiv.vaddConst ℝ (-v)) p = p - v := by rfl
    have hv0 : (AffineIsometryEquiv.vaddConst ℝ (-v)) 0 = -v := by simp
    rw [hvp, hv0]
    simp only [rotationMap, map_sub, map_neg]
    abel

end MovingSofa
