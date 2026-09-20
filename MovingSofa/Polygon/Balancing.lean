import MovingSofa.Polygon.Balancing.Estimate
import MovingSofa.Polygon.Height.PositiveIncrement

noncomputable section

namespace MovingSofa

private lemma exists_pos_lt_of_quadratic_error {f : ℝ → ℝ} {a C η δ : ℝ}
    (ha : 0 < a) (hC : 0 ≤ C) (hη : 0 < η) (hδ : 0 < δ)
    (herror : ∀ ε, 0 ≤ ε → ε ≤ η → |f ε - f 0 - a * ε| ≤ C * ε ^ 2) :
    ∃ ε, 0 < ε ∧ ε < δ ∧ f 0 < f ε := by
  let ε := min (η / 2) (min (δ / 2) (a / (2 * (C + 1))))
  have hε : 0 < ε := lt_min (half_pos hη)
    (lt_min (half_pos hδ) (div_pos ha (by positivity)))
  have hεη : ε ≤ η := (min_le_left _ _).trans (by linarith)
  have hεδ : ε < δ := (min_le_right _ _).trans_lt
    ((min_le_left _ _).trans_lt (by linarith))
  have hεa : ε ≤ a / (2 * (C + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hprod : ε * (2 * (C + 1)) ≤ a :=
    (le_div_iff₀ (by positivity : 0 < 2 * (C + 1))).mp hεa
  have hsmall : C * ε < a := by nlinarith
  have hquad : C * ε ^ 2 < a * ε := by nlinarith [mul_pos (sub_pos.mpr hsmall) hε]
  have hlower := (abs_le.mp (herror ε hε.le hεη)).1
  exact ⟨ε, hε, hεδ, by linarith⟩

/-- A support-height increment has the balancing first-order area term. -/
theorem polygonCap_balancing_estimate {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (t : angleDomain Θ) :
    ∃ C η : ℝ, 0 ≤ C ∧ 0 < η ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ η →
      |polygonHeightArea (raisedPolygonSupport K t ε) -
        polygonHeightArea (raisedPolygonSupport K t 0) -
        ((surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}).toReal -
          polygonCapPolylineLength K t) * ε| ≤ C * ε ^ 2 := by
  by_cases ht : t.val ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)
  · exact polygonCap_balancing_estimate_of_endpoint K t ht
  · exact polygonCap_balancing_estimate_of_not_endpoint K t ht

/-- A maximum polygon cap has balanced boundary coefficients. -/
theorem maximumPolygonCap_balanced {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (hK : IsMaximumPolygonCap Θ K) : IsBalancedPolygonCap K := by
  classical
  by_contra hnot
  obtain ⟨t, ht⟩ := polygonCap_not_balanced_positive K hnot
  have hnonneg : 0 ≤ polygonCapPolylineLength K t := by
    unfold polygonCapPolylineLength
    exact Finset.sum_nonneg (fun _ _ ↦ by split_ifs <;> positivity)
  have hfinite : surfaceAreaMeasure K.val.val {(t.val : Real.Angle)} ≠ ⊤ := by
    let := (surfaceAreaMeasure_face_union K.val.val).1
    exact MeasureTheory.measure_ne_top _ _
  have hpos : 0 < surfaceAreaMeasure K.val.val {(t.val : Real.Angle)} :=
    lt_of_le_of_lt zero_le ht
  have hgain : 0 < (surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}).toReal -
      polygonCapPolylineLength K t := by
    have hh := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hfinite).mpr ht
    rw [ENNReal.toReal_ofReal hnonneg] at hh
    exact sub_pos.mpr hh
  obtain ⟨C, η, hC, hη, herror⟩ := polygonCap_balancing_estimate K t
  obtain ⟨δ, hδ, hfeasible⟩ := polygonCap_positive_height_increment K t hpos
  obtain ⟨ε, hε, hεδ, harea⟩ := exists_pos_lt_of_quadratic_error hgain hC hη hδ herror
  obtain ⟨K', hK'⟩ := hfeasible ε hε hεδ
  obtain ⟨L, v, htranslate⟩ := K'.property
  have hreduce := polygonHeightArea_le_translateArea (raisedPolygonSupport K t ε) K' hK'.symm
  rw [(polygonTranslateExtensions_eq L v K' htranslate).2] at hreduce
  have hzero : raisedPolygonSupport K t 0 =
      (fun s ↦ supportValue (K.val.val : Set Point) (s.val : Real.Angle)) := by
    funext s
    simp [raisedPolygonSupport]
  rw [hzero, (polygonHeightNiche_of_cap K).2] at harea
  exact (not_lt_of_ge (hK.2 L)) (harea.trans_le hreduce)

end MovingSofa
