import MovingSofa.Analysis.Stieltjes.Continuous

noncomputable section

namespace MovingSofa

open MeasureTheory Set

private def unitIntervalIdentity : RightContinuousIntervalBV 0 1 where
  toFun t := t
  boundedVariation := by
    apply ((show Monotone ((↑) : Set.Icc (0 : ℝ) 1 → ℝ) from fun _ _ h ↦ h).monotoneOn
      Set.univ).boundedVariationOn (C := 1)
    intro t _
    rw [abs_of_nonneg t.property.1]
    exact t.property.2
  right_continuous t := continuous_subtype_val.continuousAt.continuousWithinAt

private theorem continuous_unitIntervalIdentity :
    Continuous unitIntervalIdentity.toFun :=
  continuous_subtype_val

/-- A continuous BV driver carries total Stieltjes mass equal to its increment. -/
theorem intervalStieltjesMeasure_univ_of_continuous {a b : ℝ} (hab : a ≤ b)
    (Q : RightContinuousIntervalBV a b) (hQ : Continuous Q.toFun) :
    intervalStieltjesMeasure Q univ =
      Q.toFun ⟨b, hab, le_rfl⟩ - Q.toFun ⟨a, le_rfl, hab⟩ := by
  have hu : (univ : Set (Icc a b)) = Icc ⟨a, le_rfl, hab⟩ ⟨b, hab, le_rfl⟩ := by
    ext x
    simp only [mem_univ, mem_Icc, true_iff]
    exact x.property
  unfold intervalStieltjesMeasure
  rw [hu, Q.boundedVariation.vectorMeasure_Icc (show
      (⟨a, le_rfl, hab⟩ : Icc a b) ≤ ⟨b, hab, le_rfl⟩ from hab),
    hQ.continuousAt.continuousWithinAt.rightLim_eq,
    hQ.continuousAt.continuousWithinAt.leftLim_eq]

/-- An affine function of a continuous BV driver has that driver's Stieltjes measure, scaled by
the affine map's slope. -/
theorem intervalStieltjesMeasure_affine {a b : ℝ}
    (Q F : RightContinuousIntervalBV a b) (hQ : Continuous Q.toFun) (u v : ℝ)
    (hF : ∀ t, F.toFun t = u + v * Q.toFun t) :
    intervalStieltjesMeasure F = v • intervalStieltjesMeasure Q := by
  have hFc : Continuous F.toFun := by
    rw [show F.toFun = fun t ↦ u + v * Q.toFun t from funext hF]
    exact continuous_const.add (continuous_const.mul hQ)
  apply VectorMeasure.ext_of_Icc
  intro x y hxy
  simp only [smul_apply]
  unfold intervalStieltjesMeasure
  rw [F.boundedVariation.vectorMeasure_Icc hxy, Q.boundedVariation.vectorMeasure_Icc hxy,
    hFc.continuousAt.continuousWithinAt.rightLim_eq,
    hFc.continuousAt.continuousWithinAt.leftLim_eq,
    hQ.continuousAt.continuousWithinAt.rightLim_eq,
    hQ.continuousAt.continuousWithinAt.leftLim_eq, hF x, hF y]
  ring

/-- Shifting a continuous BV driver and its integrand by constants shifts the interval Stieltjes
integral over the whole parameter interval by the integrand's shift times the driver's increment;
the driver's own shift has no effect. -/
theorem intervalStieltjesIntegral_add_const {a b : ℝ} (hab : a ≤ b)
    (F G : RightContinuousIntervalBV a b) (hF : Continuous F.toFun) (c : ℝ)
    (hFG : ∀ t, G.toFun t = F.toFun t + c) (g : Icc a b → ℝ) (hg : Continuous g) (d : ℝ) :
    intervalStieltjesIntegral G (fun t ↦ g t + d) univ =
      intervalStieltjesIntegral F g univ +
        d * (F.toFun ⟨b, hab, le_rfl⟩ - F.toFun ⟨a, le_rfl, hab⟩) := by
  let _ : IsFiniteMeasure (intervalStieltjesMeasure F).variation :=
    BoundedVariationOn.instIsFiniteMeasureVariationVectorMeasure F.boundedVariation
  have hmeas : intervalStieltjesMeasure G = intervalStieltjesMeasure F := by
    rw [intervalStieltjesMeasure_affine F G hF c 1 fun t ↦ by rw [hFG t]; ring, one_smul]
  have hsum : (fun t ↦ g t + d) = g + fun _ ↦ d := rfl
  rw [intervalStieltjesIntegral_univ, intervalStieltjesIntegral_univ, hmeas, hsum,
    VectorMeasure.integral_add (F.integrable_of_continuous hg)
      (F.integrable_of_continuous continuous_const),
    VectorMeasure.integral_const, ← intervalStieltjesMeasure_univ_of_continuous hab F hF]
  simp

/-- The signed cross integral of two affine functions of one continuous BV driver. -/
theorem intervalStieltjesIntegral_affine_driver_cross {a b : ℝ} (hab : a ≤ b)
    (Q F G : RightContinuousIntervalBV a b) (hQ : Continuous Q.toFun)
    (u v w z : ℝ) (hF : ∀ t, F.toFun t = u + v * Q.toFun t)
    (hG : ∀ t, G.toFun t = w + z * Q.toFun t) :
    intervalStieltjesIntegral G F.toFun univ - intervalStieltjesIntegral F G.toFun univ =
      (u * z - w * v) * (Q.toFun ⟨b, hab, le_rfl⟩ - Q.toFun ⟨a, le_rfl, hab⟩) := by
  let _ : IsFiniteMeasure (intervalStieltjesMeasure Q).variation :=
    BoundedVariationOn.instIsFiniteMeasureVariationVectorMeasure Q.boundedVariation
  have hFm := intervalStieltjesMeasure_affine Q F hQ u v hF
  have hGm := intervalStieltjesMeasure_affine Q G hQ w z hG
  have hi (H : RightContinuousIntervalBV a b) (c d : ℝ)
      (hH : ∀ t, H.toFun t = c + d * Q.toFun t) :
      intervalStieltjesIntegral Q H.toFun univ =
        c * (Q.toFun ⟨b, hab, le_rfl⟩ - Q.toFun ⟨a, le_rfl, hab⟩) +
          d * intervalStieltjesIntegral Q Q.toFun univ := by
    have heq : H.toFun = (fun _ ↦ c) + d • Q.toFun := by
      funext t
      exact hH t
    have hc := Q.integrable_of_continuous (g := fun _ ↦ c) continuous_const
    have hd := Q.integrable_of_continuous (g := d • Q.toFun) (continuous_const.smul hQ)
    unfold intervalStieltjesIntegral
    simp only [VectorMeasure.restrict_univ, heq]
    rw [VectorMeasure.integral_add hc hd, VectorMeasure.integral_smul,
      VectorMeasure.integral_const, intervalStieltjesMeasure_univ_of_continuous hab Q hQ]
    simp
  have hFI := hi F u v hF
  have hGI := hi G w z hG
  unfold intervalStieltjesIntegral at hFI hGI ⊢
  simp only [VectorMeasure.restrict_univ] at hFI hGI ⊢
  rw [hFm, hGm, VectorMeasure.integral_smul_vectorMeasure,
    VectorMeasure.integral_smul_vectorMeasure, hFI, hGI]
  ring


theorem intervalStieltjesIntegral_affine_cross
    (F G : RightContinuousIntervalBV 0 1) (a b c d : ℝ)
    (hF : ∀ t, F.toFun t = a + b * (t : ℝ))
    (hG : ∀ t, G.toFun t = c + d * (t : ℝ)) :
    intervalStieltjesIntegral G F.toFun Set.univ -
        intervalStieltjesIntegral F G.toFun Set.univ = a * d - c * b := by
  simpa only [unitIntervalIdentity, sub_zero, mul_one] using
    intervalStieltjesIntegral_affine_driver_cross (by norm_num : (0 : ℝ) ≤ 1)
      unitIntervalIdentity F G continuous_unitIntervalIdentity a b c d hF hG

end MovingSofa
