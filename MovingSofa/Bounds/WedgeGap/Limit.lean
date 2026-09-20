import MovingSofa.Analysis.SurfaceMeasure.AtomLimits
import MovingSofa.ForMathlib.Order.Infimum
import MovingSofa.Bounds.WedgeGap.Infimum

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace MovingSofa

theorem wedgeGapInfimum_hausdorff_bound {ω : ℝ} (K L : CapSpace ω)
    (hω : ω < Real.pi / 2) :
    |(wedgeGapInfimum K).1 - (wedgeGapInfimum L).1| ≤
      (1 + (Real.cos ω)⁻¹) * Metric.hausdorffDist (K.val : Set Point) L.val := by
  let d := Metric.hausdorffDist (K.val : Set Point) L.val
  let C := (1 + (Real.cos ω)⁻¹) * d
  let f := fun t : ℝ ↦ (wedgeGaps K t).1
  let g := fun t : ℝ ↦ (wedgeGaps L t).1
  have hω0 : 0 < ω := K.property.1
  have hcosω : 0 < Real.cos ω := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, hω0], hω⟩
  have hcost {t : ℝ} (ht : t ∈ Icc 0 ω) : 0 < Real.cos t :=
    Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos, ht.1], ht.2.trans_lt hω⟩
  have hsupport := compactSet_support_continuity (K.val : Set Point) (L.val : Set Point)
    K.val.nonempty K.val.isCompact L.val.nonempty L.val.isCompact
  have hsupport' (t : ℝ) :
      |supportValue K.val (t : Real.Angle) - supportValue L.val (t : Real.Angle)| ≤ d := by
    change |vectorSupport (K.val : Set Point) (normalVector (t : Real.Angle)) -
      vectorSupport (L.val : Set Point) (normalVector (t : Real.Angle))| ≤ d
    exact hsupport.2.1 _ (norm_normalVector_real t)
  have hpoint (t : ℝ) (ht : t ∈ Ioo 0 ω) : |f t - g t| ≤ C := by
    have hct : 0 < Real.cos t := hcost ⟨ht.1.le, ht.2.le⟩
    have hcos_le : Real.cos ω ≤ Real.cos t :=
      Real.cos_le_cos_of_nonneg_of_le_pi ht.1.le
        (by linarith [Real.pi_pos, hω]) ht.2.le
    dsimp only [f, g]
    rw [wedgeGaps_fst_eq_supportValue, wedgeGaps_fst_eq_supportValue]
    calc
      |(supportValue K.val (0 : Real.Angle) -
          (supportValue K.val (t : Real.Angle) - 1) / Real.cos t) -
        (supportValue L.val (0 : Real.Angle) -
          (supportValue L.val (t : Real.Angle) - 1) / Real.cos t)| =
          |(supportValue K.val (0 : Real.Angle) -
              supportValue L.val (0 : Real.Angle)) -
            (supportValue K.val (t : Real.Angle) -
              supportValue L.val (t : Real.Angle)) / Real.cos t| := by
            congr 1
            field_simp
            ring
      _ ≤ |supportValue K.val (0 : Real.Angle) -
            supportValue L.val (0 : Real.Angle)| +
          |(supportValue K.val (t : Real.Angle) -
            supportValue L.val (t : Real.Angle)) / Real.cos t| := abs_sub _ _
      _ = |supportValue K.val (0 : Real.Angle) -
            supportValue L.val (0 : Real.Angle)| +
          |supportValue K.val (t : Real.Angle) -
            supportValue L.val (t : Real.Angle)| / Real.cos t := by
            rw [abs_div, abs_of_pos hct]
      _ ≤ d + d / Real.cos t := add_le_add (hsupport' 0)
        (div_le_div_of_nonneg_right (hsupport' t) hct.le)
      _ ≤ d + d / Real.cos ω := add_le_add le_rfl
        (div_le_div_of_nonneg_left Metric.hausdorffDist_nonneg hcosω hcos_le)
      _ = C := by simp only [C, div_eq_mul_inv]; ring
  have hf_cont : ContinuousOn f (Icc 0 ω) := by
    have hnum : Continuous fun t : ℝ ↦
        supportValue K.val (t : Real.Angle) - 1 :=
      (hsupport.2.2.1.comp Real.Angle.continuous_coe).sub continuous_const
    have hquot : ContinuousOn (fun t : ℝ ↦
        (supportValue K.val (t : Real.Angle) - 1) / Real.cos t) (Icc 0 ω) :=
      hnum.continuousOn.div Real.continuous_cos.continuousOn
        (fun t ht ↦ (hcost ht).ne')
    have hf_eq : f = fun t : ℝ ↦ supportValue K.val (0 : Real.Angle) -
        (supportValue K.val (t : Real.Angle) - 1) / Real.cos t := by
      funext t
      exact wedgeGaps_fst_eq_supportValue K t
    rw [hf_eq]
    convert continuousOn_const.sub hquot using 1
  have hsupportL := compactSet_support_continuity (L.val : Set Point) (K.val : Set Point)
    L.val.nonempty L.val.isCompact K.val.nonempty K.val.isCompact
  have hg_cont : ContinuousOn g (Icc 0 ω) := by
    have hnum : Continuous fun t : ℝ ↦
        supportValue L.val (t : Real.Angle) - 1 :=
      (hsupportL.2.2.1.comp Real.Angle.continuous_coe).sub continuous_const
    have hquot : ContinuousOn (fun t : ℝ ↦
        (supportValue L.val (t : Real.Angle) - 1) / Real.cos t) (Icc 0 ω) :=
      hnum.continuousOn.div Real.continuous_cos.continuousOn
        (fun t ht ↦ (hcost ht).ne')
    have hg_eq : g = fun t : ℝ ↦ supportValue L.val (0 : Real.Angle) -
        (supportValue L.val (t : Real.Angle) - 1) / Real.cos t := by
      funext t
      exact wedgeGaps_fst_eq_supportValue L t
    rw [hg_eq]
    convert continuousOn_const.sub hquot using 1
  have hf : BddBelow (f '' Ioo 0 ω) :=
    (IsCompact.bddBelow_image isCompact_Icc hf_cont).mono (image_mono Ioo_subset_Icc_self)
  have hg : BddBelow (g '' Ioo 0 ω) :=
    (IsCompact.bddBelow_image isCompact_Icc hg_cont).mono (image_mono Ioo_subset_Icc_self)
  simpa only [wedgeGapInfimum, f, g, C, d] using
    abs_sInf_image_sub_sInf_image_le (nonempty_Ioo.mpr hω0) f g hf hg hpoint

/-- The left wedge-gap infimum obeys the same Hausdorff estimate as the right one. -/
theorem wedgeGapInfimum_snd_hausdorff_bound {ω : ℝ} (K L : CapSpace ω)
    (hω : ω < Real.pi / 2) :
    |(wedgeGapInfimum K).2 - (wedgeGapInfimum L).2| ≤
      (1 + (Real.cos ω)⁻¹) * Metric.hausdorffDist (K.val : Set Point) L.val := by
  let d := Metric.hausdorffDist (K.val : Set Point) L.val
  let C := (1 + (Real.cos ω)⁻¹) * d
  let f := fun t : ℝ ↦ (wedgeGaps K t).2
  let g := fun t : ℝ ↦ (wedgeGaps L t).2
  have hω0 : 0 < ω := K.property.1
  have hcosω : 0 < Real.cos ω := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, hω0], hω⟩
  have hcosδ {t : ℝ} (ht : t ∈ Icc 0 ω) : 0 < Real.cos (ω - t) :=
    Real.cos_pos_of_mem_Ioo
      ⟨by linarith [ht.2], by linarith [Real.pi_pos, ht.1, hω]⟩
  have hsupport := compactSet_support_continuity (K.val : Set Point) (L.val : Set Point)
    K.val.nonempty K.val.isCompact L.val.nonempty L.val.isCompact
  have hsupport' (t : ℝ) :
      |supportValue K.val (t : Real.Angle) - supportValue L.val (t : Real.Angle)| ≤ d := by
    change |vectorSupport (K.val : Set Point) (normalVector (t : Real.Angle)) -
      vectorSupport (L.val : Set Point) (normalVector (t : Real.Angle))| ≤ d
    exact hsupport.2.1 _ (norm_normalVector_real t)
  have hpoint (t : ℝ) (ht : t ∈ Ioo 0 ω) : |f t - g t| ≤ C := by
    have hct : 0 < Real.cos (ω - t) := hcosδ ⟨ht.1.le, ht.2.le⟩
    have hcos_le : Real.cos ω ≤ Real.cos (ω - t) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (sub_nonneg.mpr ht.2.le)
        (by linarith [Real.pi_pos, hω]) (by linarith [ht.1])
    dsimp only [f, g]
    rw [wedgeGaps_snd_eq_supportValue, wedgeGaps_snd_eq_supportValue]
    calc
      |(supportValue K.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) -
          (supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
            Real.cos (ω - t)) -
        (supportValue L.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) -
          (supportValue L.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
            Real.cos (ω - t))| =
          |(supportValue K.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) -
              supportValue L.val ((ω + Real.pi / 2 : ℝ) : Real.Angle)) -
            (supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) -
              supportValue L.val ((t + Real.pi / 2 : ℝ) : Real.Angle)) /
                Real.cos (ω - t)| := by
            congr 1
            field_simp
            ring
      _ ≤ |supportValue K.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) -
            supportValue L.val ((ω + Real.pi / 2 : ℝ) : Real.Angle)| +
          |(supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) -
            supportValue L.val ((t + Real.pi / 2 : ℝ) : Real.Angle)) /
              Real.cos (ω - t)| := abs_sub _ _
      _ = |supportValue K.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) -
            supportValue L.val ((ω + Real.pi / 2 : ℝ) : Real.Angle)| +
          |supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) -
            supportValue L.val ((t + Real.pi / 2 : ℝ) : Real.Angle)| /
              Real.cos (ω - t) := by
            rw [abs_div, abs_of_pos hct]
      _ ≤ d + d / Real.cos (ω - t) := add_le_add (hsupport' (ω + Real.pi / 2))
        (div_le_div_of_nonneg_right (hsupport' (t + Real.pi / 2)) hct.le)
      _ ≤ d + d / Real.cos ω := add_le_add le_rfl
        (div_le_div_of_nonneg_left Metric.hausdorffDist_nonneg hcosω hcos_le)
      _ = C := by simp only [C, div_eq_mul_inv]; ring
  have hf_cont : ContinuousOn f (Icc 0 ω) := by
    have hnum : Continuous fun t : ℝ ↦
        supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 :=
      (hsupport.2.2.1.comp
        (Real.Angle.continuous_coe.comp (continuous_id.add continuous_const))).sub
          continuous_const
    have hquot : ContinuousOn (fun t : ℝ ↦
        (supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
          Real.cos (ω - t)) (Icc 0 ω) :=
      hnum.continuousOn.div
        (Real.continuous_cos.comp (continuous_const.sub continuous_id)).continuousOn
        (fun t ht ↦ (hcosδ ht).ne')
    have hf_eq : f = fun t : ℝ ↦
        supportValue K.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) -
          (supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
            Real.cos (ω - t) := by
      funext t
      exact wedgeGaps_snd_eq_supportValue K t
    rw [hf_eq]
    exact continuousOn_const.sub hquot
  have hsupportL := compactSet_support_continuity (L.val : Set Point) (K.val : Set Point)
    L.val.nonempty L.val.isCompact K.val.nonempty K.val.isCompact
  have hg_cont : ContinuousOn g (Icc 0 ω) := by
    have hnum : Continuous fun t : ℝ ↦
        supportValue L.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 :=
      (hsupportL.2.2.1.comp
        (Real.Angle.continuous_coe.comp (continuous_id.add continuous_const))).sub
          continuous_const
    have hquot : ContinuousOn (fun t : ℝ ↦
        (supportValue L.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
          Real.cos (ω - t)) (Icc 0 ω) :=
      hnum.continuousOn.div
        (Real.continuous_cos.comp (continuous_const.sub continuous_id)).continuousOn
        (fun t ht ↦ (hcosδ ht).ne')
    have hg_eq : g = fun t : ℝ ↦
        supportValue L.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) -
          (supportValue L.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
            Real.cos (ω - t) := by
      funext t
      exact wedgeGaps_snd_eq_supportValue L t
    rw [hg_eq]
    exact continuousOn_const.sub hquot
  have hf : BddBelow (f '' Ioo 0 ω) :=
    (IsCompact.bddBelow_image isCompact_Icc hf_cont).mono (image_mono Ioo_subset_Icc_self)
  have hg : BddBelow (g '' Ioo 0 ω) :=
    (IsCompact.bddBelow_image isCompact_Icc hg_cont).mono (image_mono Ioo_subset_Icc_self)
  simpa only [wedgeGapInfimum, f, g, C, d] using
    abs_sInf_image_sub_sInf_image_le (nonempty_Ioo.mpr hω0) f g hf hg hpoint

theorem balancedMaximumCap_gap_le_surface {ω : ℝ} (K : CapSpace ω)
    (hK : IsBalancedMaximumCap K) (hω : ω < Real.pi / 2) :
    (wedgeGapInfimum K).1 ≤
      (surfaceAreaMeasure K.val {((Real.pi / 2 : ℝ) : Real.Angle)}).toReal ∧
    (wedgeGapInfimum K).2 ≤
      (surfaceAreaMeasure K.val {(ω : Real.Angle)}).toReal := by
  obtain ⟨n, hn, _hmono, _hdyadic, P, hmax, hlim⟩ := hK
  let Θ (i : ℕ) := uniformAngleSet ω K.property.1 K.property.2.1 (n i) (hn i)
  have hpolygon (i : ℕ) := maximumPolygonCap_gap_le_surface (P i) (hmax i) hω
  have hfst : Tendsto (fun i ↦ (wedgeGapInfimum (P i).val).1) atTop
      (𝓝 (wedgeGapInfimum K).1) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ ↦ dist_nonneg) _ (by
      simpa only [mul_zero] using
        Tendsto.const_mul (1 + (Real.cos ω)⁻¹) hlim)
    intro i
    simpa only [Real.dist_eq, uniformAngleSet] using
      wedgeGapInfimum_hausdorff_bound (P i).val K hω
  have hsnd : Tendsto (fun i ↦ (wedgeGapInfimum (P i).val).2) atTop
      (𝓝 (wedgeGapInfimum K).2) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ ↦ dist_nonneg) _ (by
      simpa only [mul_zero] using
        Tendsto.const_mul (1 + (Real.cos ω)⁻¹) hlim)
    intro i
    simpa only [Real.dist_eq, uniformAngleSet] using
      wedgeGapInfimum_snd_hausdorff_bound (P i).val K hω
  constructor
  · exact le_surfaceAreaMeasure_atom_of_tendsto hlim hfst (fun i ↦ (hpolygon i).1)
  · apply le_surfaceAreaMeasure_atom_of_tendsto hlim hsnd
    intro i
    simpa only [Θ, uniformAngleSet] using (hpolygon i).2

end MovingSofa
