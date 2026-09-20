import MovingSofa.Curve.SmoothIntervalPaths
import MovingSofa.Geometry.FrameCalculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

noncomputable section
namespace MovingSofa

/-- A Lipschitz map on the unit circle induces a continuous BV loop in increasing angular order. -/
def radialBVLoop (f : {u : Point | ‖u‖ = 1} → Point) {C : NNReal}
    (hf : LipschitzWith C f) : ContinuousBVPaths 0 (2 * Real.pi) := by
  let n : Set.Icc (0 : ℝ) (2 * Real.pi) → {u : Point | ‖u‖ = 1} :=
    fun t ↦ ⟨normalVector ((t : ℝ) : Real.Angle), norm_normalVector_real t⟩
  have hn : LipschitzWith 1 n := by
    apply LipschitzWith.of_dist_le_mul
    intro t u
    exact lipschitzWith_normalVector_real.dist_le_mul t.val u.val
  exact continuousBVOfLipschitz (f ∘ n) (hf.comp hn)

/-- The radial BV loop evaluates by applying the circle map to the angular normal. -/
lemma radialBVLoop_apply (f : {u : Point | ‖u‖ = 1} → Point) {C : NNReal}
    (hf : LipschitzWith C f) (t : Set.Icc (0 : ℝ) (2 * Real.pi)) :
    (radialBVLoop f hf).val t =
      f ⟨normalVector ((t : ℝ) : Real.Angle), norm_normalVector_real t⟩ := rfl

/-- The radial BV loop has equal endpoints. -/
lemma radialBVLoop_closed (f : {u : Point | ‖u‖ = 1} → Point) {C : NNReal}
    (hf : LipschitzWith C f) :
    (radialBVLoop f hf).val ⟨0, le_rfl, by positivity⟩ =
      (radialBVLoop f hf).val ⟨2 * Real.pi, by positivity, le_rfl⟩ := by
  rw [radialBVLoop_apply, radialBVLoop_apply]
  apply congrArg f
  apply Subtype.ext
  ext i
  fin_cases i <;> simp [normalVector, frame]

/-- An injective circle map gives a radial loop injective before its final endpoint. -/
lemma radialBVLoop_injOn (f : {u : Point | ‖u‖ = 1} → Point) {C : NNReal}
    (hf : LipschitzWith C f) (hinj : Function.Injective f) :
    Set.InjOn (radialBVLoop f hf).val {t | (t : ℝ) < 2 * Real.pi} := by
  intro t ht u hu h
  let : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  rw [radialBVLoop_apply, radialBVLoop_apply] at h
  have hn := congrArg Subtype.val (hinj h)
  have ha : (t.val : Real.Angle) = (u.val : Real.Angle) := by
    apply Real.Angle.cos_sin_inj
    · exact congrFun (congrArg WithLp.ofLp hn) 0
    · exact congrFun (congrArg WithLp.ofLp hn) 1
  apply Subtype.ext
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico
    (show t.val ∈ Set.Ico 0 (0 + 2 * Real.pi) from ⟨t.property.1, by simpa using ht⟩)
    (show u.val ∈ Set.Ico 0 (0 + 2 * Real.pi) from ⟨u.property.1, by simpa using hu⟩)).mp ha

/-- The radial BV loop has the same range as the underlying unit-circle map. -/
lemma range_radialBVLoop (f : {u : Point | ‖u‖ = 1} → Point) {C : NNReal}
    (hf : LipschitzWith C f) : Set.range (radialBVLoop f hf).val = Set.range f := by
  apply Set.Subset.antisymm
  · rintro p ⟨t, rfl⟩
    exact ⟨_, (radialBVLoop_apply f hf t).symm⟩
  · rintro p ⟨u, rfl⟩
    obtain ⟨θ, hθ⟩ := exists_angle_normalVector_eq u.property
    let : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
    let t := AddCircle.equivIco (2 * Real.pi) 0 θ
    have ht : (t.val : Real.Angle) = θ := AddCircle.coe_equivIco
    refine ⟨⟨t.val, t.property.1, ?_⟩, ?_⟩
    · simpa using t.property.2.le
    · rw [radialBVLoop_apply]
      apply congrArg f
      apply Subtype.ext
      exact (congrArg normalVector ht).trans hθ

end MovingSofa
