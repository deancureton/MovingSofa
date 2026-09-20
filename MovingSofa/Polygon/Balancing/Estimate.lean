import MovingSofa.Polygon.Height.WallVariation
import MovingSofa.Polygon.Balancing.Coefficients
import MovingSofa.Polygon.Height.Properties
import MovingSofa.Polygon.Height.RaisedSupport

noncomputable section

namespace MovingSofa

private def polygonCapSupportHeight {Θ : AngleSet} (K : PolygonCapSpace Θ) :
    PolygonHeightSpace Θ :=
  fun s ↦ supportValue K.val.val (s.val : Real.Angle)

private theorem raisedPolygonSupport_eq_update {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (t : angleDomain Θ) (varepsilon : ℝ) :
    raisedPolygonSupport K t varepsilon =
      Function.update (polygonCapSupportHeight K) t
        (polygonCapSupportHeight K t + varepsilon) := by
  classical
  unfold raisedPolygonSupport polygonCapSupportHeight PolygonHeightSpace
  funext s
  by_cases hst : s = t
  · subst s
    simp
  · simp [Function.update, hst]

private theorem raisedPolygonSupport_zero {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (t : angleDomain Θ) : raisedPolygonSupport K t 0 = polygonCapSupportHeight K := by
  unfold raisedPolygonSupport polygonCapSupportHeight PolygonHeightSpace
  funext s
  simp

private theorem update_sub_one {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    (t : angleDomain Θ) (varepsilon : ℝ) :
    Function.update (fun s ↦ h s - 1) t (h t - 1 + varepsilon) =
      fun s ↦ Function.update h t (h t + varepsilon) s - 1 := by
  classical
  change angleDomain Θ → ℝ at h
  funext s
  by_cases hst : s = t
  · subst s
    simp
    ring
  · simp [Function.update, hst]

private theorem polygonHeightCap_supportHeight {Θ : AngleSet} (K : PolygonCapSpace Θ) :
    polygonHeightCap (polygonCapSupportHeight K) = K.val.val := by
  let K' : PolygonCapTranslateSpace Θ :=
    ⟨K.val.val, ⟨K, 0, by simp⟩⟩
  change polygonHeightCap
    (fun s ↦ supportValue K.val.val (s.val : Real.Angle)) = K.val.val
  exact polygonHeightCap_of_translate K'

private theorem polygonHeightNiche_supportHeight {Θ : AngleSet} (K : PolygonCapSpace Θ) :
    polygonHeightNiche (polygonCapSupportHeight K) = polygonNiche Θ K.val := by
  change polygonHeightNiche
    (fun s ↦ supportValue K.val.val (s.val : Real.Angle)) = polygonNiche Θ K.val
  exact (polygonHeightNiche_of_cap K).1

private theorem independentWallCap_update_eq_of_not_endpoint {Θ : AngleSet}
    (h : PolygonHeightSpace Θ) (t : angleDomain Θ) (varepsilon : ℝ)
    (ht : t.val ∉ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
    independentWallCap (Function.update h t (h t + varepsilon)) (fun s ↦ h s - 1) =
      polygonHeightCap (Function.update h t (h t + varepsilon)) := by
  classical
  calc
    independentWallCap (Function.update h t (h t + varepsilon)) (fun s ↦ h s - 1) =
        independentWallCap (Function.update h t (h t + varepsilon))
          (fun s ↦ Function.update h t (h t + varepsilon) s - 1) := by
      ext p
      simp only [independentWallCap, Set.mem_inter_iff, Set.mem_iInter]
      apply and_congr
      · apply forall_congr'
        intro s
        apply forall_congr'
        intro hs
        have hst : (⟨s, Or.inr hs⟩ : angleDomain Θ) ≠ t := by
          intro hst
          apply ht
          have hval : s = t.val := congrArg Subtype.val hst
          rwa [hval] at hs
        simp [polygonHeightValue, Function.update, hst]
      · rfl
    _ = polygonHeightCap (Function.update h t (h t + varepsilon)) :=
      independentWallCap_sub_one (Θ := Θ) _

private theorem independentWallCap_update_both_eq {Θ : AngleSet}
    (h : PolygonHeightSpace Θ) (t : angleDomain Θ) (varepsilon : ℝ) :
    independentWallCap (Function.update h t (h t + varepsilon))
        (Function.update (fun s ↦ h s - 1) t (h t - 1 + varepsilon)) =
      polygonHeightCap (Function.update h t (h t + varepsilon)) := by
  rw [update_sub_one]
  exact independentWallCap_sub_one (Θ := Θ) _

private theorem independentWallNiche_update_eq {Θ : AngleSet}
    (h : PolygonHeightSpace Θ) (t : angleDomain Θ) (varepsilon : ℝ) :
    independentWallNiche
        (Function.update (fun s ↦ h s - 1) t (h t - 1 + varepsilon)) =
      polygonHeightNiche (Function.update h t (h t + varepsilon)) := by
  rw [update_sub_one]
  exact independentWallNiche_sub_one (Θ := Θ) _

/-- The balancing area estimate when the perturbed normal is not an endpoint. -/
theorem polygonCap_balancing_estimate_of_not_endpoint {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (t : angleDomain Θ)
    (ht : t.val ∉ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
    ∃ C eta : ℝ, 0 ≤ C ∧ 0 < eta ∧ ∀ varepsilon : ℝ,
      0 ≤ varepsilon → varepsilon ≤ eta →
      |polygonHeightArea (raisedPolygonSupport K t varepsilon) -
        polygonHeightArea (raisedPolygonSupport K t 0) -
        ((surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}).toReal -
          polygonCapPolylineLength K t) * varepsilon| ≤ C * varepsilon ^ 2 := by
  classical
  let h := polygonCapSupportHeight K
  obtain ⟨⟨nc, Hc, hHc, hSc⟩, ⟨nn, Hn, hHn, hSn⟩⟩ := polygonCap_niche_simpleNef Θ h
  have htInner : t.val ∈ (Θ.directions : Set ℝ) ∪
      ((fun s : ℝ ↦ s + Real.pi / 2) '' Θ.directions) := by
    rcases t.property with htInner | htEndpoint
    · exact htInner
    · exact False.elim (ht htEndpoint)
  have hcMem :
      (⟨(t.val : Real.Angle), h t, false, false⟩ : PlanarHalfPlaneData) ∈
        Set.range Hc := by
    rw [hHc]
    exact Or.inl ⟨t.val, t.property, by simp [polygonHeightValue]⟩
  obtain ⟨ic, hic⟩ := hcMem
  have hnMem :
      (⟨(t.val : Real.Angle), h t - 1, false, true⟩ : PlanarHalfPlaneData) ∈
        Set.range Hn := by
    rw [hHn]
    exact Or.inl ⟨t.val, htInner, by simp [polygonHeightValue, t.property]⟩
  obtain ⟨in_, hin⟩ := hnMem
  obtain ⟨Cc, etac, hCc, hetac, hcap⟩ :=
    polygonCap_upper_wall_area_variation h Hc hHc hSc.1 ic t hic
  obtain ⟨tn, Cn, etan, htnAngle, hCn, hetan, hniche⟩ :=
    polygonNiche_wall_area_variation h Hn hHn hSn.1 in_
  have hinAngle : (Hn in_).angle = (t.val : Real.Angle) := by rw [hin]
  have htn : tn = t := angleDomain_coe_injective Θ (htnAngle.symm.trans hinAngle)
  subst tn
  have hcapCoeff :
      (MeasureTheory.Measure.hausdorffMeasure 1
        (frontier (polygonHeightCap h) ∩ (Hc ic).boundaryLine)).toReal =
        (surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}).toReal := by
    rw [polygonHeightCap_supportHeight K, hic]
    simpa [PlanarHalfPlaneData.boundaryLine, h, polygonCapSupportHeight] using
      congrArg ENNReal.toReal
        (hausdorffMeasure_frontier_inter_supportingLine K.val.val
          (t.val : Real.Angle))
  have hnicheCoeff :
      (MeasureTheory.Measure.hausdorffMeasure 1
        (frontier (polygonHeightNiche h) ∩ (Hn in_).boundaryLine)).toReal =
        polygonCapPolylineLength K t := by
    rw [polygonHeightNiche_supportHeight K, hin]
    simpa [nicheBoundaryLength, PlanarHalfPlaneData.boundaryLine, h,
      polygonCapSupportHeight] using nicheBoundaryLength_lowerLine_of_not_endpoint K t ht
  refine ⟨Cc + Cn, min etac etan, add_nonneg hCc hCn, lt_min hetac hetan, ?_⟩
  intro varepsilon hvarepsilon hvarepsilonEta
  have hvarepsilonC : |varepsilon| ≤ etac := by
    rw [abs_of_nonneg hvarepsilon]
    exact hvarepsilonEta.trans (min_le_left _ _)
  have hvarepsilonN : |varepsilon| ≤ etan := by
    rw [abs_of_nonneg hvarepsilon]
    exact hvarepsilonEta.trans (min_le_right _ _)
  have hc := hcap varepsilon hvarepsilonC
  have hn := hniche varepsilon hvarepsilonN
  rw [hcapCoeff, independentWallCap_update_eq_of_not_endpoint h t varepsilon ht] at hc
  rw [hnicheCoeff, independentWallNiche_update_eq h t varepsilon] at hn
  simp only [hin, Bool.false_eq_true, ite_false, one_mul] at hn
  rw [raisedPolygonSupport_eq_update K t varepsilon, raisedPolygonSupport_zero K t,
    polygonHeightArea]
  change
    |(ClassicalResults.area (polygonHeightCap (Function.update h t (h t + varepsilon))) -
        ClassicalResults.area (polygonHeightNiche (Function.update h t (h t + varepsilon)))) -
      (ClassicalResults.area (polygonHeightCap h) -
        ClassicalResults.area (polygonHeightNiche h)) -
      ((surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}).toReal -
        polygonCapPolylineLength K t) * varepsilon| ≤
      (Cc + Cn) * varepsilon ^ 2
  calc
    _ = |(ClassicalResults.area
          (polygonHeightCap (Function.update h t (h t + varepsilon))) -
        ClassicalResults.area (polygonHeightCap h) -
        (surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}).toReal * varepsilon) -
      (ClassicalResults.area
          (polygonHeightNiche (Function.update h t (h t + varepsilon))) -
        ClassicalResults.area (polygonHeightNiche h) -
        polygonCapPolylineLength K t * varepsilon)| := by ring_nf
    _ ≤ |ClassicalResults.area
          (polygonHeightCap (Function.update h t (h t + varepsilon))) -
        ClassicalResults.area (polygonHeightCap h) -
        (surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}).toReal * varepsilon| +
      |ClassicalResults.area
          (polygonHeightNiche (Function.update h t (h t + varepsilon))) -
        ClassicalResults.area (polygonHeightNiche h) -
        polygonCapPolylineLength K t * varepsilon| := abs_sub _ _
    _ ≤ Cc * varepsilon ^ 2 + Cn * varepsilon ^ 2 := add_le_add hc hn
    _ = (Cc + Cn) * varepsilon ^ 2 := by ring

/-- The balancing area estimate for a simultaneous endpoint-wall displacement. -/
theorem polygonCap_balancing_estimate_of_endpoint {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (t : angleDomain Θ)
    (ht : t.val ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
    ∃ C eta : ℝ, 0 ≤ C ∧ 0 < eta ∧ ∀ varepsilon : ℝ,
      0 ≤ varepsilon → varepsilon ≤ eta →
      |polygonHeightArea (raisedPolygonSupport K t varepsilon) -
        polygonHeightArea (raisedPolygonSupport K t 0) -
        ((surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}).toReal -
          polygonCapPolylineLength K t) * varepsilon| ≤ C * varepsilon ^ 2 := by
  classical
  let h := polygonCapSupportHeight K
  obtain ⟨⟨nc, Hc, hHc, hSc⟩, ⟨nn, Hn, hHn, hSn⟩⟩ := polygonCap_niche_simpleNef Θ h
  have hcuMem :
      (⟨(t.val : Real.Angle), h t, false, false⟩ : PlanarHalfPlaneData) ∈
        Set.range Hc := by
    rw [hHc]
    exact Or.inl ⟨t.val, t.property, by simp [polygonHeightValue]⟩
  obtain ⟨icu, hicu⟩ := hcuMem
  have hclMem :
      (⟨(t.val : Real.Angle), h t - 1, true, false⟩ : PlanarHalfPlaneData) ∈
        Set.range Hc := by
    rw [hHc]
    exact Or.inr ⟨t.val, ht, by simp [polygonHeightValue, t.property]⟩
  obtain ⟨icl, hicl⟩ := hclMem
  have hnMem :
      (⟨(t.val : Real.Angle), h t - 1, true, false⟩ : PlanarHalfPlaneData) ∈
        Set.range Hn := by
    rw [hHn]
    exact Or.inr ⟨t.val, ht, by simp [polygonHeightValue, t.property]⟩
  obtain ⟨in_, hin⟩ := hnMem
  obtain ⟨Cu, etau, hCu, hetau, hcapUpper⟩ :=
    polygonCap_upper_wall_area_variation h Hc hHc hSc.1 icu t hicu
  obtain ⟨Cl, etal, hCl, hetal, hcapLower⟩ :=
    polygonCap_lower_wall_area_variation h Hc hHc hSc.1 icl t hicl
  obtain ⟨tn, Cn, etan, htnAngle, hCn, hetan, hniche⟩ :=
    polygonNiche_wall_area_variation h Hn hHn hSn.1 in_
  have hinAngle : (Hn in_).angle = (t.val : Real.Angle) := by rw [hin]
  have htn : tn = t := angleDomain_coe_injective Θ (htnAngle.symm.trans hinAngle)
  subst tn
  obtain ⟨R, epsilonZero, hR, hepsilonZero, huniform⟩ :=
    polygonPerturbation_uniform_bounds Θ h
  have hupperCoeff :
      (MeasureTheory.Measure.hausdorffMeasure 1
        (frontier (polygonHeightCap h) ∩ (Hc icu).boundaryLine)).toReal =
        (surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}).toReal := by
    rw [polygonHeightCap_supportHeight K, hicu]
    simpa [PlanarHalfPlaneData.boundaryLine, h, polygonCapSupportHeight] using
      congrArg ENNReal.toReal
        (hausdorffMeasure_frontier_inter_supportingLine K.val.val
          (t.val : Real.Angle))
  have hlowerCoeff :
      (MeasureTheory.Measure.hausdorffMeasure 1
        (frontier (polygonHeightCap h) ∩ (Hc icl).boundaryLine)).toReal =
        (surfaceAreaMeasure K.val.val
          {((t.val + Real.pi : ℝ) : Real.Angle)}).toReal := by
    rw [polygonHeightCap_supportHeight K, hicl]
    simpa [PlanarHalfPlaneData.boundaryLine, h, polygonCapSupportHeight] using
      congrArg ENNReal.toReal
        (hausdorffMeasure_frontier_inter_lowerLine_of_endpoint K ht)
  have hnicheCoeff :
      (MeasureTheory.Measure.hausdorffMeasure 1
        (frontier (polygonHeightNiche h) ∩ (Hn in_).boundaryLine)).toReal =
        (surfaceAreaMeasure K.val.val
          {((t.val + Real.pi : ℝ) : Real.Angle)}).toReal -
          polygonCapPolylineLength K t := by
    rw [polygonHeightNiche_supportHeight K, hin]
    simpa [nicheBoundaryLength, PlanarHalfPlaneData.boundaryLine, h,
      polygonCapSupportHeight] using nicheBoundaryLength_lowerLine_of_endpoint K t ht
  let eta := min etau (min etal (min etan (min epsilonZero 1)))
  refine ⟨Cu + Cl + Cn, eta, add_nonneg (add_nonneg hCu hCl) hCn,
    lt_min hetau (lt_min hetal (lt_min hetan (lt_min hepsilonZero zero_lt_one))), ?_⟩
  intro varepsilon hvarepsilon hvarepsilonEta
  have hvarepsilonU : |varepsilon| ≤ etau := by
    rw [abs_of_nonneg hvarepsilon]
    exact hvarepsilonEta.trans (by simp [eta])
  have hvarepsilonL : |varepsilon| ≤ etal := by
    rw [abs_of_nonneg hvarepsilon]
    exact hvarepsilonEta.trans (by simp [eta])
  have hvarepsilonN : |varepsilon| ≤ etan := by
    rw [abs_of_nonneg hvarepsilon]
    exact hvarepsilonEta.trans (by simp [eta])
  have hvarepsilonZero : varepsilon ≤ epsilonZero :=
    hvarepsilonEta.trans (by simp [eta])
  have hvarepsilonOne : varepsilon ≤ 1 :=
    hvarepsilonEta.trans (by simp [eta])
  have hu := hcapUpper varepsilon hvarepsilonU
  have hl := hcapLower varepsilon hvarepsilonL
  have hn := hniche varepsilon hvarepsilonN
  rw [hupperCoeff] at hu
  rw [hlowerCoeff] at hl
  rw [hnicheCoeff, independentWallNiche_update_eq h t varepsilon] at hn
  simp [hin] at hn
  have hchangeUpper (s : angleDomain Θ) :
      |Function.update h t (h t + varepsilon) s - h s| ≤ epsilonZero := by
    by_cases hst : s = t
    · subst s
      have hself : Function.update h t (h t + varepsilon) t = h t + varepsilon :=
        Function.update_self t (h t + varepsilon) h
      rw [hself]
      simpa [abs_of_nonneg hvarepsilon] using hvarepsilonZero
    · simp [Function.update, hst, le_of_lt hepsilonZero]
  have hchangeLower (s : angleDomain Θ) :
      |Function.update (fun r ↦ h r - 1) t (h t - 1 + varepsilon) s -
        (h s - 1)| ≤ epsilonZero := by
    by_cases hst : s = t
    · subst s
      have hself :
          Function.update (fun r ↦ h r - 1) t (h t - 1 + varepsilon) t =
            h t - 1 + varepsilon :=
        Function.update_self t (h t - 1 + varepsilon) (fun r ↦ h r - 1)
      rw [hself]
      simpa [abs_of_nonneg hvarepsilon] using hvarepsilonZero
    · simp [Function.update, hst, le_of_lt hepsilonZero]
  have hbound (upper lower : PolygonHeightSpace Θ)
      (hupper : upper = h ∨ upper = Function.update h t (h t + varepsilon))
      (hlower : lower = (fun s ↦ h s - 1) ∨
        lower = Function.update (fun s ↦ h s - 1) t (h t - 1 + varepsilon)) :
      independentWallCap upper lower ⊆ Metric.closedBall 0 R := by
    apply (huniform upper lower ?_ ?_).1
    · rcases hupper with rfl | rfl
      · intro s
        simp [le_of_lt hepsilonZero]
      · exact hchangeUpper
    · rcases hlower with rfl | rfl
      · intro s
        simp [le_of_lt hepsilonZero]
      · exact hchangeLower
  have hadd := independentWallCap_area_update_add h t varepsilon R
    hvarepsilon hvarepsilonOne hbound
  rw [independentWallCap_update_both_eq h t varepsilon,
    independentWallCap_sub_one (Θ := Θ)] at hadd
  rw [raisedPolygonSupport_eq_update K t varepsilon, raisedPolygonSupport_zero K t,
    polygonHeightArea]
  change
    |(ClassicalResults.area (polygonHeightCap (Function.update h t (h t + varepsilon))) -
        ClassicalResults.area (polygonHeightNiche (Function.update h t (h t + varepsilon)))) -
      (ClassicalResults.area (polygonHeightCap h) -
        ClassicalResults.area (polygonHeightNiche h)) -
      ((surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}).toReal -
        polygonCapPolylineLength K t) * varepsilon| ≤
      (Cu + Cl + Cn) * varepsilon ^ 2
  let upperResidual :=
    ClassicalResults.area
        (independentWallCap (Function.update h t (h t + varepsilon)) (fun s ↦ h s - 1)) -
      ClassicalResults.area (polygonHeightCap h) -
      (surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}).toReal * varepsilon
  let lowerResidual :=
    ClassicalResults.area
        (independentWallCap h
          (Function.update (fun s ↦ h s - 1) t (h t - 1 + varepsilon))) -
      ClassicalResults.area (polygonHeightCap h) +
      (surfaceAreaMeasure K.val.val
        {((t.val + Real.pi : ℝ) : Real.Angle)}).toReal * varepsilon
  let nicheResidual :=
    ClassicalResults.area (polygonHeightNiche (Function.update h t (h t + varepsilon))) -
      ClassicalResults.area (polygonHeightNiche h) +
      ((surfaceAreaMeasure K.val.val
        {((t.val + Real.pi : ℝ) : Real.Angle)}).toReal -
        polygonCapPolylineLength K t) * varepsilon
  have hn' : |nicheResidual| ≤ Cn * varepsilon ^ 2 := by
    dsimp [nicheResidual]
    convert hn using 1
    ring_nf
  have hresidual :
      (ClassicalResults.area (polygonHeightCap (Function.update h t (h t + varepsilon))) -
          ClassicalResults.area
            (polygonHeightNiche (Function.update h t (h t + varepsilon)))) -
        (ClassicalResults.area (polygonHeightCap h) -
          ClassicalResults.area (polygonHeightNiche h)) -
        ((surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}).toReal -
          polygonCapPolylineLength K t) * varepsilon =
      upperResidual + lowerResidual - nicheResidual := by
    dsimp [upperResidual, lowerResidual, nicheResidual]
    linarith [hadd]
  rw [hresidual]
  calc
    |upperResidual + lowerResidual - nicheResidual| ≤
        |upperResidual + lowerResidual| + |nicheResidual| := abs_sub _ _
    _ ≤ (|upperResidual| + |lowerResidual|) + |nicheResidual| :=
      add_le_add (abs_add_le _ _) (le_refl _)
    _ ≤ (Cu * varepsilon ^ 2 + Cl * varepsilon ^ 2) + Cn * varepsilon ^ 2 := by
      exact add_le_add (add_le_add hu hl) hn'
    _ = (Cu + Cl + Cn) * varepsilon ^ 2 := by ring

end MovingSofa
