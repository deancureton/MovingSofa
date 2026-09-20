import MovingSofa.Cap.CornerPaths
import MovingSofa.Cap.CornerMeasure
import MovingSofa.Cap.Special.Domain
import MovingSofa.Area.Variation
import MovingSofa.Convex.CombinationPullback

/-!
# The inner-corner variation on the middle window

On the middle window `I = [φᴿ, φᴸ]` the inner corner of a special cap is
`(h_K(t) - 1) • u_t + (h_K(t + π/2) - 1) • v_t`, an affine expression in two support values, so it
depends convex-linearly on the cap. `capInnerCorner_variation` pulls the quadratic curve-area
functional back along that convex-linear map, which gives quadraticity of
`K ↦ 𝒥(x_K|_I)` and reduces its directional derivative to the curve-variation formula.

The remaining work is to recognize the two mixed Stieltjes integrals of that formula as the
pairing of the support increment against the corner measure. The inner corner is `C¹` on the cap
domain by the injectivity condition, so its Stieltjes measure is its classical velocity times
Lebesgue measure; the frame identity `planeCrossProduct_eq_inner_frame` then turns the pointwise
cross product into the corner density against the support increment, on `I` and on `I + π/2`
separately.
-/

noncomputable section

open MeasureTheory

namespace MovingSofa

/-! ### The middle window -/

/-- The two distinguished Gerver angles are positive, ordered, and below `π / 2`, so the middle
window `[φᴿ, φᴸ]` and its quarter turn are disjoint subsets of `[0, π]`. -/
private theorem middleWindow_bounds :
    0 < paperGerverConstants.2.1 ∧ paperGerverConstants.2.1 ≤ paperGerverConstants.2.2 ∧
      paperGerverConstants.2.2 < Real.pi / 2 := by
  obtain ⟨hr, hl, hsum⟩ := paperGerverConstants_snd_mem_Ioo
  have hle : paperGerverConstants.2.1 ≤ Real.pi / 4 := by
    have h := GerversSofa.ABφθSpec.existsUnique.choose_spec.1
    exact le_trans h.2.1 h.2.2.1
  exact ⟨hr.1, by linarith only [hle, hsum], hl.2⟩

/-- The middle window lies inside the cap's angular domain. -/
private theorem middleWindow_subset :
    Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2 ⊆ Set.Icc 0 (Real.pi / 2) := by
  obtain ⟨hrpos, -, hlpi⟩ := middleWindow_bounds
  exact Set.Icc_subset_Icc hrpos.le hlpi.le

/-! ### Regularity of the inner corner of a special cap -/

/-- The inner corner of a special cap is continuously differentiable on the cap domain. -/
private theorem specialCap_contDiffOn (K : SpecialCapSpace) :
    ContDiffOn ℝ 1 (capInnerCorner K.val) (Set.Icc 0 (Real.pi / 2)) :=
  K.property.1.2.1

/-- At an interior time the inner corner of a special cap has an honest derivative. -/
private theorem specialCap_hasDerivAt (K : SpecialCapSpace) {t : ℝ}
    (ht : t ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (capInnerCorner K.val)
      (derivWithin (capInnerCorner K.val) (Set.Icc 0 (Real.pi / 2)) t) t :=
  ((specialCap_contDiffOn K).differentiableOn one_ne_zero t
    (Set.Ioo_subset_Icc_self ht)).hasDerivWithinAt.hasDerivAt (Icc_mem_nhds ht.1 ht.2)

/-! ### The corner density on the two middle windows -/

/-- On the right middle window the corner density is the tangent velocity component. -/
private theorem capCornerDensity_eq_right (K : SpecialCapSpace) {s : ℝ}
    (hs : s ∈ Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2) :
    capCornerDensity K s = (capVelocityCoefficients K s).2 := by
  obtain ⟨hrpos, -, hlpi⟩ := middleWindow_bounds
  rw [capCornerDensity, ite_eq_left ⟨lt_of_lt_of_le hrpos hs.1, hs.2.trans hlpi.le⟩]

/-- On the left middle window the corner density is the shifted normal velocity component. -/
private theorem capCornerDensity_eq_left (K : SpecialCapSpace) {s : ℝ}
    (hs : s ∈ Set.Icc (Real.pi / 2 + paperGerverConstants.2.1)
      (Real.pi / 2 + paperGerverConstants.2.2)) :
    capCornerDensity K s = -(capVelocityCoefficients K (s - Real.pi / 2)).1 := by
  obtain ⟨hrpos, -, hlpi⟩ := middleWindow_bounds
  have h1 : Real.pi / 2 < s := by linarith [hs.1]
  have h2 : s ≤ Real.pi := by linarith [hs.2]
  rw [capCornerDensity, ite_eq_right (by rintro ⟨-, h⟩; linarith), ite_eq_left ⟨h1, h2⟩]

/-- The corner density is nonnegative on the middle windows, by the injectivity signs. -/
private theorem capCornerDensity_nonneg_middle (K : SpecialCapSpace) {s : ℝ}
    (hs : s ∈ Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2 ∪
      Set.Icc (Real.pi / 2 + paperGerverConstants.2.1)
        (Real.pi / 2 + paperGerverConstants.2.2)) :
    0 ≤ capCornerDensity K s := by
  obtain ⟨hrpos, -, hlpi⟩ := middleWindow_bounds
  have hsign := K.property.1.2.2
  rcases hs with hs | hs
  · rw [capCornerDensity_eq_right K hs]
    exact (hsign s ⟨lt_of_lt_of_le hrpos hs.1, lt_of_le_of_lt hs.2 hlpi⟩).2.le
  · rw [capCornerDensity_eq_left K hs]
    have hmem : s - Real.pi / 2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [hs.1], by linarith [hs.2]⟩
    exact neg_nonneg.mpr (hsign _ hmem).1.le

/-- The corner density is continuous on each of the two middle windows. -/
private theorem continuousOn_capCornerDensity_middle (K : SpecialCapSpace) :
    ContinuousOn (capCornerDensity K)
        (Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2) ∧
      ContinuousOn (capCornerDensity K)
        (Set.Icc (Real.pi / 2 + paperGerverConstants.2.1)
          (Real.pi / 2 + paperGerverConstants.2.2)) := by
  obtain ⟨hα, hβ⟩ := continuousOn_capVelocityCoefficients K
  refine ⟨(hβ.mono middleWindow_subset).congr fun s hs ↦ capCornerDensity_eq_right K hs, ?_⟩
  have hmaps : Set.MapsTo (fun s : ℝ ↦ s - Real.pi / 2)
      (Set.Icc (Real.pi / 2 + paperGerverConstants.2.1)
        (Real.pi / 2 + paperGerverConstants.2.2))
      (Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2) := by
    intro s hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  refine ContinuousOn.congr ?_ fun s hs ↦ capCornerDensity_eq_left K hs
  exact (((hα.mono middleWindow_subset).comp
    (continuous_id.sub continuous_const).continuousOn hmaps)).neg

/-! ### Integrating against the corner angle measure -/

/-- On a parameter window inside `[0, π]` the corner angle measure integrates a continuous
function against the real corner density. -/
private theorem setIntegral_capCornerAngleMeasure (K : SpecialCapSpace) {S : Set ℝ}
    (hSmeas : MeasurableSet S) (hS : S ⊆ Set.Icc 0 Real.pi)
    (hd : AEMeasurable (capCornerDensity K) (volume.restrict S))
    (hdpos : ∀ s ∈ S, 0 ≤ capCornerDensity K s) {f : Real.Angle → ℝ} (hf : Continuous f) :
    ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' S, f t ∂capCornerAngleMeasure K =
      ∫ s in S, capCornerDensity K s * f (s : Real.Angle) := by
  have hcoe : Measurable fun s : ℝ ↦ (s : Real.Angle) := Real.Angle.continuous_coe.measurable
  have hturn : Real.pi ≤ -1 + 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hSIoc : S ⊆ Set.Ioc (-1) Real.pi := fun s hs ↦ ⟨by linarith [(hS hs).1], (hS hs).2⟩
  have himg : MeasurableSet ((fun s : ℝ ↦ (s : Real.Angle)) '' S) :=
    Real.Angle.measurableSet_image_of_subset_Ioc hturn hSmeas hSIoc
  have hApre : MeasurableSet ((fun s : ℝ ↦ (s : Real.Angle)) ⁻¹'
      ((fun s : ℝ ↦ (s : Real.Angle)) '' S)) := himg.preimage hcoe
  have hAS : ((fun s : ℝ ↦ (s : Real.Angle)) ⁻¹'
      ((fun s : ℝ ↦ (s : Real.Angle)) '' S)) ∩ Set.Icc 0 Real.pi = S := by
    refine Set.Subset.antisymm ?_ fun s hs ↦ ⟨⟨s, hs, rfl⟩, hS hs⟩
    rintro x ⟨⟨s, hs, hxs⟩, hx⟩
    have hxIoc : x ∈ Set.Ioc (-1) Real.pi := ⟨by linarith [hx.1], hx.2⟩
    exact (Real.Angle.injOn_coe_Ioc hturn (hSIoc hs) hxIoc hxs) ▸ hs
  have h1 : ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' S, f t ∂capCornerAngleMeasure K =
      ∫ s in (fun s : ℝ ↦ (s : Real.Angle)) ⁻¹' ((fun s : ℝ ↦ (s : Real.Angle)) '' S),
        f (s : Real.Angle) ∂capCornerMeasure K := by
    rw [capCornerAngleMeasure]
    exact setIntegral_map himg hf.aestronglyMeasurable hcoe.aemeasurable
  have hrestrict : (volume.restrict (Set.Icc 0 Real.pi)).restrict
      ((fun s : ℝ ↦ (s : Real.Angle)) ⁻¹' ((fun s : ℝ ↦ (s : Real.Angle)) '' S)) =
      volume.restrict S := by
    rw [Measure.restrict_restrict hApre, hAS]
  have haem : AEMeasurable (fun s ↦ ENNReal.ofReal (capCornerDensity K s))
      ((volume.restrict (Set.Icc 0 Real.pi)).restrict
        ((fun s : ℝ ↦ (s : Real.Angle)) ⁻¹' ((fun s : ℝ ↦ (s : Real.Angle)) '' S))) := by
    rw [hrestrict]
    exact ENNReal.measurable_ofReal.comp_aemeasurable hd
  have h2 : ∫ s in (fun s : ℝ ↦ (s : Real.Angle)) ⁻¹' ((fun s : ℝ ↦ (s : Real.Angle)) '' S),
        f (s : Real.Angle) ∂capCornerMeasure K =
      ∫ s in (fun s : ℝ ↦ (s : Real.Angle)) ⁻¹' ((fun s : ℝ ↦ (s : Real.Angle)) '' S),
        (ENNReal.ofReal (capCornerDensity K s)).toReal • f (s : Real.Angle)
          ∂volume.restrict (Set.Icc 0 Real.pi) := by
    rw [capCornerMeasure]
    exact setIntegral_withDensity_eq_setIntegral_toReal_smul₀ haem
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top) _ hApre
  rw [h1, h2]
  change ∫ s, _ ∂((volume.restrict (Set.Icc 0 Real.pi)).restrict _) = _
  rw [hrestrict]
  refine setIntegral_congr_fun hSmeas fun s hs ↦ ?_
  rw [ENNReal.toReal_ofReal (hdpos s hs), smul_eq_mul]

/-! ### The middle Stieltjes integrals as weighted Lebesgue integrals -/

/-- The middle corner path's Stieltjes measure has the inner-corner velocity as density. -/
private theorem capMiddle_stieltjesDensity (K : SpecialCapSpace) (i : Fin 2) :
    HasIntervalStieltjesDensity (continuousBVCoordinate (capMiddleBV K) i)
      (fun t ↦ derivWithin (capInnerCorner K.val) (Set.Icc 0 (Real.pi / 2)) t i) := by
  obtain ⟨hrpos, hrl, hlpi⟩ := middleWindow_bounds
  have hproj : ContDiff ℝ 1 fun p : Point ↦ p i :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff
  refine hasIntervalStieltjesDensity_of_hasDerivAt hrl _
    (fun s ↦ capInnerCorner K.val s i) _ (fun _ ↦ rfl) ?_ ?_ ?_
  · refine ContDiffOn.absolutelyContinuousOnInterval ?_
    rw [Set.uIcc_of_le hrl]
    exact hproj.comp_contDiffOn ((specialCap_contDiffOn K).mono middleWindow_subset)
  · intro t ht
    have ht' : t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hrpos.trans ht.1, ht.2.trans hlpi⟩
    exact (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp_hasDerivAt t
      (specialCap_hasDerivAt K ht')
  · exact (((PiLp.continuous_apply 2 _ i).comp_continuousOn
      ((continuousOn_derivWithin_capInnerCorner K).mono middleWindow_subset))).integrableOn_compact
        isCompact_Icc

/-- A mixed Stieltjes integral over the middle window is the corresponding weighted Lebesgue
integral of the inner-corner velocity. -/
private theorem capMiddle_stieltjesIntegral_eq (K L : SpecialCapSpace) (i j : Fin 2) :
    intervalStieltjesIntegral (continuousBVCoordinate (capMiddleBV K) i)
        (fun t ↦ (capMiddleBV L).val t j - (capMiddleBV K).val t j) Set.univ =
      ∫ t in Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2,
        (capInnerCorner L.val t j - capInnerCorner K.val t j) *
          derivWithin (capInnerCorner K.val) (Set.Icc 0 (Real.pi / 2)) t i := by
  have hq : Continuous fun t : Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2 ↦
      (capMiddleBV L).val t j - (capMiddleBV K).val t j :=
    ((PiLp.continuous_apply 2 _ j).comp (capMiddleBV L).property.1).sub
      ((PiLp.continuous_apply 2 _ j).comp (capMiddleBV K).property.1)
  have hval : ∀ (M : SpecialCapSpace)
      (t : Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2),
      (capMiddleBV M).val t = capInnerCorner M.val t.val := fun _ _ ↦ rfl
  rw [intervalStieltjesIntegral_eq_integral_mul_of_density _ (capMiddle_stieltjesDensity K i)
    hq Set.univ MeasurableSet.univ, Measure.restrict_univ]
  simp only [hval]
  have key := MeasureTheory.integral_subtype_preimage (μ := volume)
    (s := Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2) measurableSet_Icc
    (MeasurableSet.univ (α := ℝ))
    (fun t : ℝ ↦ (capInnerCorner L.val t j - capInnerCorner K.val t j) *
      derivWithin (capInnerCorner K.val) (Set.Icc 0 (Real.pi / 2)) t i)
  simp only [Set.mem_univ, Set.ofPred_true, Measure.restrict_univ] at key
  exact key

/-! ### The variation of the inner corner -/

theorem capInnerCorner_variation :
    IsConvexLinear specialCapCombination bvPathCombination capMiddleBV ∧
    IsQuadraticFunctional specialCapCombination (fun K ↦ curveAreaFunctional (capMiddleBV K)) ∧
    ∀ K L : SpecialCapSpace,
      convexDirectionalDerivative specialCapCombination
        (fun M ↦ curveAreaFunctional (capMiddleBV M)) K L =
      (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) ''
          (Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2 ∪
            Set.Icc (Real.pi / 2 + paperGerverConstants.2.1)
              (Real.pi / 2 + paperGerverConstants.2.2)),
        (supportValue L.val.val t - supportValue K.val.val t) ∂capCornerAngleMeasure K) +
        (segmentArea (distinguishedCapSides K.val).2.corner
            (distinguishedCapSides L.val).2.corner -
          segmentArea (distinguishedCapSides K.val).1.corner
            (distinguishedCapSides L.val).1.corner) := by
  obtain ⟨hrpos, hrl, hlpi⟩ := middleWindow_bounds
  -- ### The middle corner path is convex-linear
  have hlinear : IsConvexLinear specialCapCombination bvPathCombination capMiddleBV := by
    intro t K L
    refine Subtype.ext (funext fun s ↦ ?_)
    show capInnerCorner (specialCapCombination t K L).val s.val = _
    rw [capInnerCorner_of_eq_convexBodyCombination (specialCap_isConvexDomain.1 t K L)]
    rfl
  refine ⟨hlinear, (curveArea_variation _ _ hrl).1.comp_isConvexLinear hlinear, ?_⟩
  intro K L
  rw [convexDirectionalDerivative_comp_isConvexLinear hlinear _ K L,
    (curveArea_variation _ _ hrl).2]
  refine congrArg₂ (· + ·) ?_ rfl
  -- ### The middle window and the corner density on it
  have hSmeas : MeasurableSet (Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2 ∪
      Set.Icc (Real.pi / 2 + paperGerverConstants.2.1)
        (Real.pi / 2 + paperGerverConstants.2.2)) := measurableSet_Icc.union measurableSet_Icc
  have hSsub : Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2 ∪
      Set.Icc (Real.pi / 2 + paperGerverConstants.2.1)
        (Real.pi / 2 + paperGerverConstants.2.2) ⊆ Set.Icc 0 Real.pi := by
    have hpi := Real.pi_pos
    rintro s (hs | hs)
    · exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    · exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  obtain ⟨hdc1, hdc2⟩ := continuousOn_capCornerDensity_middle K
  have hd : AEMeasurable (capCornerDensity K)
      (volume.restrict (Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2 ∪
        Set.Icc (Real.pi / 2 + paperGerverConstants.2.1)
          (Real.pi / 2 + paperGerverConstants.2.2))) :=
    (hdc1.union_of_isClosed hdc2 isClosed_Icc isClosed_Icc).aemeasurable hSmeas
  have hcont (M : ConvexBody Point) : Continuous fun u : Real.Angle ↦ supportValue M u :=
    (compactSet_support_continuity M M M.nonempty M.isCompact M.nonempty M.isCompact).2.2.1
  have hfcont : Continuous fun u : Real.Angle ↦ supportValue (L.val.val : Set Point) u -
      supportValue (K.val.val : Set Point) u := (hcont L.val.val).sub (hcont K.val.val)
  have hfreal : Continuous fun s : ℝ ↦ supportValue (L.val.val : Set Point) (s : Real.Angle) -
      supportValue (K.val.val : Set Point) (s : Real.Angle) :=
    hfcont.comp Real.Angle.continuous_coe
  -- ### Continuity of the four Lebesgue integrands on the middle window
  have hXc : ContinuousOn (capInnerCorner K.val)
      (Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2) :=
    ((specialCap_contDiffOn K).mono middleWindow_subset).continuousOn
  have hYc : ContinuousOn (capInnerCorner L.val)
      (Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2) :=
    ((specialCap_contDiffOn L).mono middleWindow_subset).continuousOn
  have hDc : ContinuousOn (derivWithin (capInnerCorner K.val) (Set.Icc 0 (Real.pi / 2)))
      (Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2) :=
    (continuousOn_derivWithin_capInnerCorner K).mono middleWindow_subset
  have hmixed (i j : Fin 2) : IntegrableOn
      (fun t ↦ (capInnerCorner L.val t j - capInnerCorner K.val t j) *
        derivWithin (capInnerCorner K.val) (Set.Icc 0 (Real.pi / 2)) t i)
      (Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2) :=
    ((((PiLp.continuous_apply 2 _ j).comp_continuousOn hYc).sub
      ((PiLp.continuous_apply 2 _ j).comp_continuousOn hXc)).mul
      ((PiLp.continuous_apply 2 _ i).comp_continuousOn hDc)).integrableOn_compact isCompact_Icc
  have hG1 : IntegrableOn (fun s ↦ capCornerDensity K s *
      (supportValue (L.val.val : Set Point) (s : Real.Angle) -
        supportValue (K.val.val : Set Point) (s : Real.Angle)))
      (Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2) :=
    (hdc1.mul hfreal.continuousOn).integrableOn_compact isCompact_Icc
  have hG2 : IntegrableOn (fun s ↦ capCornerDensity K s *
      (supportValue (L.val.val : Set Point) (s : Real.Angle) -
        supportValue (K.val.val : Set Point) (s : Real.Angle)))
      (Set.Icc (Real.pi / 2 + paperGerverConstants.2.1)
        (Real.pi / 2 + paperGerverConstants.2.2)) :=
    (hdc2.mul hfreal.continuousOn).integrableOn_compact isCompact_Icc
  have hmaps : Set.MapsTo (fun t : ℝ ↦ t + Real.pi / 2)
      (Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2)
      (Set.Icc (Real.pi / 2 + paperGerverConstants.2.1)
        (Real.pi / 2 + paperGerverConstants.2.2)) :=
    fun s hs ↦ ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hG2' : IntegrableOn (fun t ↦ capCornerDensity K (t + Real.pi / 2) *
      (supportValue (L.val.val : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) -
        supportValue (K.val.val : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle)))
      (Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2) :=
    (((hdc2.mul hfreal.continuousOn).comp
      (continuous_id.add continuous_const).continuousOn hmaps)).integrableOn_compact isCompact_Icc
  -- ### Both sides are Lebesgue integrals over the middle window
  rw [capMiddle_stieltjesIntegral_eq K L 1 0, capMiddle_stieltjesIntegral_eq K L 0 1,
    setIntegral_capCornerAngleMeasure K hSmeas hSsub hd
      (fun s hs ↦ capCornerDensity_nonneg_middle K hs) hfcont,
    setIntegral_union (Set.disjoint_left.mpr fun s hs hs' ↦ by linarith [hs.2, hs'.1])
      measurableSet_Icc hG1 hG2,
    integral_Icc_const_add_eq (Real.pi / 2),
    ← integral_sub (hmixed 1 0) (hmixed 0 1), ← integral_add hG1 hG2']
  -- ### The pointwise cross-product identity
  refine setIntegral_congr_fun measurableSet_Icc fun t ht ↦ ?_
  have hts : t + Real.pi / 2 ∈ Set.Icc (Real.pi / 2 + paperGerverConstants.2.1)
      (Real.pi / 2 + paperGerverConstants.2.2) := hmaps ht
  have hdens1 : capCornerDensity K t =
      inner ℝ (derivWithin (capInnerCorner K.val) (Set.Icc 0 (Real.pi / 2)) t)
        (tangentVector (t : Real.Angle)) := capCornerDensity_eq_right K ht
  have hdens2 : capCornerDensity K (t + Real.pi / 2) =
      -inner ℝ (derivWithin (capInnerCorner K.val) (Set.Icc 0 (Real.pi / 2)) t)
        (normalVector (t : Real.Angle)) := by
    rw [capCornerDensity_eq_left K hts]
    simp only [add_sub_cancel_right, capVelocityCoefficients]
  have hu : inner ℝ (capInnerCorner L.val t - capInnerCorner K.val t)
      (normalVector (t : Real.Angle)) =
      supportValue (L.val.val : Set Point) (t : Real.Angle) -
        supportValue (K.val.val : Set Point) (t : Real.Angle) := by
    rw [inner_sub_left, inner_capInnerCorner_normalVector, inner_capInnerCorner_normalVector]
    ring
  have hv : inner ℝ (capInnerCorner L.val t - capInnerCorner K.val t)
      (tangentVector (t : Real.Angle)) =
      supportValue (L.val.val : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) -
        supportValue (K.val.val : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) := by
    rw [inner_sub_left, inner_capInnerCorner_tangentVector, inner_capInnerCorner_tangentVector]
    ring
  have hframe := planeCrossProduct_eq_inner_frame
    (capInnerCorner L.val t - capInnerCorner K.val t)
    (derivWithin (capInnerCorner K.val) (Set.Icc 0 (Real.pi / 2)) t) t
  have hs0 : (capInnerCorner L.val t - capInnerCorner K.val t) 0 =
      capInnerCorner L.val t 0 - capInnerCorner K.val t 0 := by simp
  have hs1 : (capInnerCorner L.val t - capInnerCorner K.val t) 1 =
      capInnerCorner L.val t 1 - capInnerCorner K.val t 1 := by simp
  rw [planeCrossProduct, hs0, hs1] at hframe
  rw [hdens1, hdens2, ← hu, ← hv]
  linear_combination hframe

end MovingSofa
