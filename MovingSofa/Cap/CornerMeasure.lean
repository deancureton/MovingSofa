import MovingSofa.Cap.Tail.Space
import MovingSofa.Geometry.FrameCalculus
import MovingSofa.ForMathlib.MeasureTheory.Angle

noncomputable section

open MeasureTheory

namespace MovingSofa

def capVelocityCoefficients (K : SpecialCapSpace) (t : ℝ) : ℝ × ℝ :=
  (inner ℝ (derivWithin (capInnerCorner K.val) (Set.Icc 0 (Real.pi / 2)) t)
      (normalVector (t : Real.Angle)),
    inner ℝ (derivWithin (capInnerCorner K.val) (Set.Icc 0 (Real.pi / 2)) t)
      (tangentVector (t : Real.Angle)))

def capCornerDensity (K : SpecialCapSpace) (s : ℝ) : ℝ :=
  if 0 < s ∧ s ≤ Real.pi / 2 then (capVelocityCoefficients K s).2
  else if Real.pi / 2 < s ∧ s ≤ Real.pi then
    -(capVelocityCoefficients K (s - Real.pi / 2)).1
  else 0

def capCornerMeasure (K : SpecialCapSpace) : Measure ℝ :=
  (volume.restrict (Set.Icc 0 Real.pi)).withDensity
    (fun s ↦ ENNReal.ofReal (capCornerDensity K s))

def capCornerAngleMeasure (K : SpecialCapSpace) : Measure Real.Angle :=
  Measure.map (fun s : ℝ ↦ (s : Real.Angle)) (capCornerMeasure K)

def capCornerMeasureData (K : SpecialCapSpace) :
    (ℝ → ℝ) × Measure ℝ × Measure Real.Angle :=
  (capCornerDensity K, capCornerMeasure K, capCornerAngleMeasure K)

/-- The corner measure of a special cap reads its density on the angular image of every
measurable subset of `[0, π]`. -/
theorem capCornerAngleMeasure_angleImage_eq_setLIntegral (K : SpecialCapSpace) {T : Set ℝ}
    (hT : MeasurableSet T) (hT' : T ⊆ Set.Icc 0 Real.pi) :
    capCornerAngleMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' T) =
      ∫⁻ s in T, ENNReal.ofReal (capCornerDensity K s) := by
  have hturn : Real.pi ≤ -1 + 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hsub : Set.Icc (0 : ℝ) Real.pi ⊆ Set.Ioc (-1 : ℝ) Real.pi :=
    fun x hx ↦ ⟨by linarith [hx.1], hx.2⟩
  show Measure.map (fun s : ℝ ↦ (s : Real.Angle))
      ((volume.restrict (Set.Icc 0 Real.pi)).withDensity
        (fun s ↦ ENNReal.ofReal (capCornerDensity K s)))
      ((fun s : ℝ ↦ (s : Real.Angle)) '' T) = _
  exact Real.Angle.map_coe_withDensity_image_eq_setLIntegral hturn hsub hT hT'

/-! ### Regularity and signs of the corner density

The injectivity condition makes the inner corner continuously differentiable on the closed
quarter turn, so both frame coefficients of its velocity are continuous there; the strict interior
signs then extend to the two endpoints by continuity.  The corner density is the sum of the two
branches extended by zero, whence its measurability and its bound. -/

/-- The inner-corner velocity of a special cap is continuous on the cap domain. -/
theorem continuousOn_derivWithin_capInnerCorner (K : SpecialCapSpace) :
    ContinuousOn (derivWithin (capInnerCorner K.val) (Set.Icc 0 (Real.pi / 2)))
      (Set.Icc 0 (Real.pi / 2)) :=
  K.property.1.2.1.continuousOn_derivWithin
    (uniqueDiffOn_Icc (by positivity : (0 : ℝ) < Real.pi / 2)) le_rfl

/-- Both frame components of the inner-corner velocity are continuous on the cap domain. -/
theorem continuousOn_capVelocityCoefficients (K : SpecialCapSpace) :
    ContinuousOn (fun s ↦ (capVelocityCoefficients K s).1) (Set.Icc 0 (Real.pi / 2)) ∧
      ContinuousOn (fun s ↦ (capVelocityCoefficients K s).2) (Set.Icc 0 (Real.pi / 2)) :=
  ⟨(continuousOn_derivWithin_capInnerCorner K).inner
      continuous_normalVector_real.continuousOn,
    (continuousOn_derivWithin_capInnerCorner K).inner
      lipschitzWith_tangentVector_real.continuous.continuousOn⟩

/-- The corner density is bounded, being continuous on the two compact halves of the cap domain
and zero outside. -/
theorem exists_bound_capCornerDensity (K : SpecialCapSpace) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s, capCornerDensity K s ≤ C := by
  obtain ⟨hα, hβ⟩ := continuousOn_capVelocityCoefficients K
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hα
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hβ
  refine ⟨max (max C₁ C₂) 0, le_max_right _ _, fun s ↦ ?_⟩
  rw [capCornerDensity]
  split_ifs with h1 h2
  · exact le_max_of_le_left (le_max_of_le_right
      ((le_abs_self _).trans (hC₂ s ⟨h1.1.le, h1.2⟩)))
  · refine le_max_of_le_left (le_max_of_le_left ?_)
    have h := neg_le_abs (capVelocityCoefficients K (s - Real.pi / 2)).1
    exact h.trans (hC₁ _ ⟨by linarith [h2.1], by linarith [h2.2]⟩)
  · exact le_max_right _ _

/-! ### Finiteness and atomlessness of the corner measure -/

instance isFiniteMeasure_capCornerMeasure (K : SpecialCapSpace) :
    IsFiniteMeasure (capCornerMeasure K) := by
  obtain ⟨C, -, hC⟩ := exists_bound_capCornerDensity K
  refine ⟨?_⟩
  rw [capCornerMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  calc ∫⁻ s, ENNReal.ofReal (capCornerDensity K s) ∂volume.restrict (Set.Icc 0 Real.pi)
      ≤ ∫⁻ _, ENNReal.ofReal C ∂volume.restrict (Set.Icc 0 Real.pi) :=
        lintegral_mono fun s ↦ ENNReal.ofReal_le_ofReal (hC s)
    _ < ⊤ := by
        rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

instance isFiniteMeasure_capCornerAngleMeasure (K : SpecialCapSpace) :
    IsFiniteMeasure (capCornerAngleMeasure K) := by
  rw [capCornerAngleMeasure]
  exact Measure.isFiniteMeasure_map _ _

instance nullSingletonClass_capCornerAngleMeasure (K : SpecialCapSpace) :
    NullSingletonClass (capCornerAngleMeasure K) := by
  refine ⟨fun x ↦ ?_⟩
  rw [capCornerAngleMeasure,
    Measure.map_apply Real.Angle.continuous_coe.measurable (measurableSet_singleton x),
    capCornerMeasure]
  exact ((withDensity_absolutelyContinuous _ _).trans
    Measure.restrict_le_self.absolutelyContinuous)
    ((Real.Angle.countable_preimage_coe_singleton x).measure_zero volume)

end MovingSofa
