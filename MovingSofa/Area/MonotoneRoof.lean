import MovingSofa.Classical.Area
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import MovingSofa.Curve.AreaAdditivity
import MovingSofa.Curve.AreaTransport
import MovingSofa.Curve.SegmentArea.Parametrization
import MovingSofa.Analysis.Stieltjes.Smooth
import MovingSofa.Analysis.Stieltjes.DensityIntegration
import MovingSofa.ForMathlib.MeasureTheory.RegionBetween

noncomputable section

namespace MovingSofa

def monotoneRoofHeight {a b : ℝ} (hab : a < b) (γ : ContinuousBVPaths a b)
    (s : ℝ) : ℝ := by
  classical
  letI : Nonempty (Set.Icc a b) := ⟨⟨a, le_rfl, hab.le⟩⟩
  exact γ.val (Function.invFun (fun t ↦ γ.val t 0) s) 1

def monotoneRoofRegion {a b : ℝ} (hab : a < b) (γ : ContinuousBVPaths a b) : Set Point :=
  {p | γ.val ⟨a, le_rfl, hab.le⟩ 0 ≤ p 0 ∧
    p 0 ≤ γ.val ⟨b, hab.le, le_rfl⟩ 0 ∧ 0 ≤ p 1 ∧
    p 1 ≤ monotoneRoofHeight hab γ (p 0)}

def monotoneRoofLoop {a b : ℝ} (hab : a < b) (γ : ContinuousBVPaths a b)
    (s : Set.Icc (0 : ℝ) 2) : Point :=
  if hs : s.val ≤ 1 then
    γ.val ⟨b - (b - a) * s.val, by
      constructor
      · nlinarith [s.property.1]
      · nlinarith [s.property.1]⟩
  else
    (2 - s.val) • γ.val ⟨a, le_rfl, hab.le⟩ +
      (s.val - 1) • γ.val ⟨b, hab.le, le_rfl⟩

theorem monotone_roof_signed_area {a b : ℝ} (hab : a < b)
    (γ : ContinuousBVPaths a b) (hk : StrictMono (fun t ↦ γ.val t 0))
    (hh : ∀ t, 0 ≤ γ.val t 1)
    (ha : γ.val ⟨a, le_rfl, hab.le⟩ 1 = 0)
    (hb : γ.val ⟨b, hab.le, le_rfl⟩ 1 = 0) :
    ∃ Γ : ContinuousBVPaths 0 2, Γ.val = monotoneRoofLoop hab γ ∧
      curveAreaFunctional Γ = ClassicalResults.area (monotoneRoofRegion hab γ) ∧
      ClassicalResults.area (monotoneRoofRegion hab γ) =
        ∫ s in γ.val ⟨a, le_rfl, hab.le⟩ 0..γ.val ⟨b, hab.le, le_rfl⟩ 0,
          monotoneRoofHeight hab γ s := by
  classical
  set A : Set.Icc a b := ⟨a, le_rfl, hab.le⟩ with hAdef
  set B : Set.Icc a b := ⟨b, hab.le, le_rfl⟩ with hBdef
  set c : ℝ := γ.val A 0 with hcdef
  set d : ℝ := γ.val B 0 with hddef
  have hAB : A < B := hab
  have hcd : c < d := hk hAB
  -- the horizontal coordinate as a map onto `[c, d]`
  have hγ0 : Continuous fun t : Set.Icc a b ↦ γ.val t 0 :=
    (PiLp.continuous_apply 2 _ 0).comp γ.property.1
  have hγ1 : Continuous fun t : Set.Icc a b ↦ γ.val t 1 :=
    (PiLp.continuous_apply 2 _ 1).comp γ.property.1
  have hmem : ∀ t : Set.Icc a b, γ.val t 0 ∈ Set.Icc c d := fun t ↦
    ⟨hk.monotone (show A ≤ t from t.property.1),
      hk.monotone (show t ≤ B from t.property.2)⟩
  set kmap : Set.Icc a b → Set.Icc c d := fun t ↦ ⟨γ.val t 0, hmem t⟩ with hkmapdef
  have hkc : Continuous kmap := hγ0.subtype_mk _
  have hkinj : Function.Injective kmap := fun x y h ↦ hk.injective (congrArg Subtype.val h)
  have : PreconnectedSpace (Set.Icc a b) := Subtype.preconnectedSpace isPreconnected_Icc
  have hksurj : Function.Surjective kmap := by
    intro s
    obtain ⟨t, ht⟩ := intermediate_value_univ A B hγ0 s.property
    exact ⟨t, Subtype.ext ht⟩
  -- the continuous monotone inverse `φ = k⁻¹`
  set khom : Set.Icc a b ≃ₜ Set.Icc c d :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective kmap ⟨hkinj, hksurj⟩) hkc
    with hkhomdef
  set φ : Set.Icc c d → Set.Icc a b := ⇑khom.symm with hφdef
  have hkhom_apply : ∀ t, khom t = kmap t := fun _ ↦ rfl
  have hφk : ∀ s : Set.Icc c d, γ.val (φ s) 0 = (s : ℝ) := by
    intro s
    have := khom.apply_symm_apply s
    rw [hkhom_apply] at this
    exact congrArg Subtype.val this
  have hφc : Continuous φ := khom.symm.continuous
  have hφs : Function.Surjective φ := khom.symm.surjective
  have hφm : Monotone φ := by
    intro s t hst
    by_contra hcon
    have hlt : φ t < φ s := lt_of_not_ge hcon
    have hlt2 := hk hlt
    simp only [hφk] at hlt2
    exact absurd hst (not_le.mpr hlt2)
  -- the roof height, as a globally continuous function on the line
  set g : ℝ → ℝ := fun s ↦ γ.val (φ (Set.projIcc c d hcd.le s)) 1 with hgdef
  have hgc : Continuous g := hγ1.comp (hφc.comp continuous_projIcc)
  have hgnonneg : ∀ s, 0 ≤ g s := fun s ↦ hh _
  have hheight : ∀ s ∈ Set.Icc c d, monotoneRoofHeight hab γ s = g s := by
    intro s hs
    have hex : ∃ t : Set.Icc a b, γ.val t 0 = s := ⟨φ ⟨s, hs⟩, hφk ⟨s, hs⟩⟩
    have hinv := @Function.invFun_eq _ _ ⟨A⟩ (fun t ↦ γ.val t 0) s hex
    have hpt : @Function.invFun _ _ ⟨A⟩ (fun t ↦ γ.val t 0) s = φ ⟨s, hs⟩ :=
      hk.injective (by simpa using hinv.trans (hφk ⟨s, hs⟩).symm)
    show γ.val (@Function.invFun _ _ ⟨A⟩ (fun t ↦ γ.val t 0) s) 1 = g s
    rw [hpt]
    simp [hgdef, Set.projIcc_of_mem _ hs]
  -- the roof region is the closed subgraph of `g` over `[c, d]`
  have hregion : monotoneRoofRegion hab γ =
      {p : Point | p 0 ∈ Set.Icc c d ∧
        p 1 ∈ Set.Icc ((fun _ : ℝ ↦ (0 : ℝ)) (p 0)) (g (p 0))} := by
    ext p
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨⟨h1, h2⟩, h3, by rwa [hheight (p 0) ⟨h1, h2⟩] at h4⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨h1, h2, h3, by rwa [hheight (p 0) ⟨h1, h2⟩]⟩
  -- the planar volume of a closed vertical subgraph
  have hvolVertical : ∀ (f₀ g₀ : ℝ → ℝ) (S : Set ℝ), Measurable f₀ → Measurable g₀ →
      MeasurableSet S → MeasureTheory.IntegrableOn f₀ S → MeasureTheory.IntegrableOn g₀ S →
      (∀ x ∈ S, f₀ x ≤ g₀ x) →
      MeasureTheory.volume {p : Point | p 0 ∈ S ∧ p 1 ∈ Set.Icc (f₀ (p 0)) (g₀ (p 0))} =
        ENNReal.ofReal (∫ x in S, (g₀ - f₀) x) := by
    intro f₀ g₀ S hf hg hS hfi hgi hfg
    have hT : MeasurableSet {q : ℝ × ℝ | q.1 ∈ S ∧ q.2 ∈ Set.Icc (f₀ q.1) (g₀ q.1)} :=
      measurableSet_region_between_cc hf hg hS
    have hpre : {p : Point | p 0 ∈ S ∧ p 1 ∈ Set.Icc (f₀ (p 0)) (g₀ (p 0))} =
        (fun p : Point ↦ (p 0, p 1)) ⁻¹'
          {q : ℝ × ℝ | q.1 ∈ S ∧ q.2 ∈ Set.Icc (f₀ q.1) (g₀ q.1)} := rfl
    rw [hpre, EuclideanSpace.volume_preserving_finTwoCoordinates.measure_preimage
      hT.nullMeasurableSet]
    rw [volume_setOf_mem_Icc_eq_volume_regionBetween hf hg hS]
    change (MeasureTheory.volume.prod MeasureTheory.volume) (regionBetween f₀ g₀ S) = _
    rw [volume_regionBetween_eq_integral hfi hgi hS hfg]
  have hgint : MeasureTheory.IntegrableOn g (Set.Icc c d) :=
    hgc.continuousOn.integrableOn_compact isCompact_Icc
  have hIcc : (∫ x in Set.Icc c d, g x) = ∫ s in c..d, g s := by
    rw [intervalIntegral.integral_of_le hcd.le, MeasureTheory.integral_Icc_eq_integral_Ioc]
  have harea : ClassicalResults.area (monotoneRoofRegion hab γ) = ∫ s in c..d, g s := by
    rw [ClassicalResults.area, hregion,
      hvolVertical (fun _ ↦ 0) g (Set.Icc c d) measurable_const hgc.measurable
        measurableSet_Icc (MeasureTheory.integrableOn_zero) hgint
        (fun x _ ↦ hgnonneg x)]
    rw [ENNReal.toReal_ofReal]
    · simp only [Pi.sub_apply, sub_zero]
      exact hIcc
    · exact MeasureTheory.integral_nonneg (fun x ↦ by simp [hgnonneg x])
  -- the two coordinate Stieltjes drivers
  have hBVext : ∀ {u v : ℝ} (F G : RightContinuousIntervalBV u v),
      F.toFun = G.toFun → F = G := by
    intro u v F G hFG
    cases F
    cases G
    simp only at hFG
    subst hFG
    rfl
  set K := continuousBVCoordinate γ 0 with hKdef
  set H := continuousBVCoordinate γ 1 with hHdef
  have hKcont : Continuous K.toFun := hγ0
  have hHcont : Continuous H.toFun := hγ1
  -- the identity driver on `[c, d]`, with Lebesgue density one
  obtain ⟨Q, hQfun, hQdens⟩ := exists_intervalBV_of_hasDerivAt hcd.le (fun x ↦ x)
    (fun _ ↦ (1 : ℝ)) (fun t ↦ hasDerivAt_id t) continuous_const
  have hstieltjes : intervalStieltjesIntegral K H.toFun Set.univ =
      intervalStieltjesIntegral Q (H.toFun ∘ φ) Set.univ := by
    rw [intervalStieltjesIntegral_comp_monotone_surjective hab.le hcd.le K hKcont
      H.toFun hHcont φ hφc hφm hφs]
    congr 1
    apply hBVext
    funext s
    show γ.val (φ s) 0 = Q.toFun s
    rw [hQfun s, hφk s]
  have hroofint : intervalStieltjesIntegral K H.toFun Set.univ = ∫ s in c..d, g s := by
    rw [hstieltjes, intervalStieltjesIntegral_eq_integral_mul_of_density Q hQdens
      (hHcont.comp hφc) Set.univ MeasurableSet.univ, MeasureTheory.Measure.restrict_univ]
    have hfun : (fun t : Set.Icc c d ↦ (H.toFun ∘ φ) t * (1 : ℝ)) =
        fun t : Set.Icc c d ↦ g (t : ℝ) := by
      funext t
      simp only [Function.comp_apply, mul_one, hgdef, Set.projIcc_val]
      rfl
    rw [hfun, MeasureTheory.integral_subtype_comap measurableSet_Icc g, hIcc]
  -- integration by parts identifies the curve area with the roof integral
  have hparts := intervalStieltjes_integration_by_parts_of_continuous a b hab.le K H
    hKcont hHcont
  have hends : K.toFun B * H.toFun B - K.toFun A * H.toFun A = 0 := by
    show γ.val B 0 * γ.val B 1 - γ.val A 0 * γ.val A 1 = 0
    rw [ha, hb]
    ring
  have hJγ : curveAreaFunctional γ = -intervalStieltjesIntegral K H.toFun Set.univ := by
    have hform : curveAreaFunctional γ =
        (intervalStieltjesIntegral H K.toFun Set.univ -
          intervalStieltjesIntegral K H.toFun Set.univ) / 2 := rfl
    rw [hform]
    rw [hends] at hparts
    linarith
  -- the reversed roof, as a path on `[a, b]`
  have hJrev := curveArea_comp_reverse hab.le γ
  set γrev : ContinuousBVPaths a b :=
    ⟨γ.val ∘ Set.Icc.reverse hab.le,
      γ.property.1.comp (Set.Icc.continuous_reverse hab.le), fun i ↦
        BoundedVariationOn.comp_antitone_surjective_Icc hab.le (γ.property.2 i)
          (Set.Icc.antitone_reverse hab.le) (Set.Icc.surjective_reverse hab.le)⟩ with hγrevdef
  change curveAreaFunctional γrev = -curveAreaFunctional γ at hJrev
  -- the antitone reparametrization of `[0, 2]` onto `[a, b]`, pausing on `[1, 2]`
  set revmap : Set.Icc (0 : ℝ) 2 → Set.Icc a b :=
    fun s ↦ Set.projIcc a b hab.le (b - (b - a) * (s : ℝ)) with hrevmapdef
  have hrevc : Continuous revmap :=
    continuous_projIcc.comp (by fun_prop)
  have hrevanti : Antitone revmap := by
    intro s t hst
    have hst' : (s : ℝ) ≤ (t : ℝ) := hst
    have hmul := mul_le_mul_of_nonneg_left hst' (sub_nonneg.mpr hab.le)
    show Set.projIcc a b hab.le (b - (b - a) * (t : ℝ)) ≤
      Set.projIcc a b hab.le (b - (b - a) * (s : ℝ))
    exact Set.monotone_projIcc hab.le (by linarith)
  have hrevsurj : Function.Surjective revmap := by
    intro t
    have hba : (0 : ℝ) < b - a := by linarith
    refine ⟨⟨(b - (t : ℝ)) / (b - a), ?_, ?_⟩, ?_⟩
    · exact div_nonneg (by linarith [t.property.2]) hba.le
    · rw [div_le_iff₀ hba]
      nlinarith [t.property.1]
    · have hval : b - (b - a) * ((b - (t : ℝ)) / (b - a)) = (t : ℝ) := by
        field_simp
        ring
      show Set.projIcc a b hab.le (b - (b - a) * ((b - (t : ℝ)) / (b - a))) = t
      rw [hval, Set.projIcc_val]
  -- the base segment piece, paused on `[0, 1]`
  set w : Point := γ.val B - γ.val A with hwdef
  set ρ : Set.Icc (0 : ℝ) 2 → Set.Icc (0 : ℝ) 1 :=
    fun s ↦ Set.projIcc 0 1 zero_le_one ((s : ℝ) - 1) with hρdef
  have hρc : Continuous ρ := continuous_projIcc.comp (by fun_prop)
  have hρm : Monotone ρ := by
    intro s t hst
    have hst' : (s : ℝ) ≤ (t : ℝ) := hst
    show Set.projIcc 0 1 zero_le_one ((s : ℝ) - 1) ≤
      Set.projIcc 0 1 zero_le_one ((t : ℝ) - 1)
    exact Set.monotone_projIcc zero_le_one (by linarith)
  have hρs : Function.Surjective ρ := by
    intro u
    refine ⟨⟨(u : ℝ) + 1, ?_, ?_⟩, ?_⟩
    · linarith [u.property.1]
    · linarith [u.property.2]
    · show Set.projIcc 0 1 zero_le_one ((u : ℝ) + 1 - 1) = u
      rw [show ((u : ℝ) + 1 - 1) = (u : ℝ) from by ring, Set.projIcc_val]
  obtain ⟨Bpath, hBpathval⟩ := continuousBVPaths_comp_monotone_surjective
    (by norm_num : (0 : ℝ) ≤ 1) (lineSegmentBVPath 0 w) ρ hρc hρm hρs
  set Apath : ContinuousBVPaths 0 2 :=
    ⟨γ.val ∘ revmap, γ.property.1.comp hrevc, fun i ↦
      BoundedVariationOn.comp_antitone_surjective_Icc hab.le (γ.property.2 i) hrevanti
        hrevsurj⟩ with hApathdef
  set Γ : ContinuousBVPaths 0 2 := Apath + Bpath with hΓdef
  have hΓval : Γ.val = monotoneRoofLoop hab γ := by
    funext s
    have h0 : (0 : ℝ) ≤ (s : ℝ) := s.property.1
    have h2 : (s : ℝ) ≤ 2 := s.property.2
    have hval : Γ.val s = γ.val (revmap s) + Path.segment (0 : Point) w (ρ s) := by
      show Apath.val s + Bpath.val s = _
      rw [hBpathval]
      rfl
    rw [hval]
    unfold monotoneRoofLoop
    split_ifs with hs
    · have hrevs : revmap s = ⟨b - (b - a) * (s : ℝ),
          by constructor <;> nlinarith⟩ := by
        show Set.projIcc a b hab.le (b - (b - a) * (s : ℝ)) = _
        exact Set.projIcc_of_mem hab.le _
      have hρ0 : ρ s = ⟨0, by norm_num⟩ := by
        show Set.projIcc 0 1 zero_le_one ((s : ℝ) - 1) = _
        exact Set.projIcc_of_le_left zero_le_one (by linarith)
      rw [hrevs, hρ0]
      simp
    · rw [not_le] at hs
      have hrevs : revmap s = A := by
        show Set.projIcc a b hab.le (b - (b - a) * (s : ℝ)) = _
        rw [Set.projIcc_of_le_left hab.le (by nlinarith)]
      have hρ1 : ρ s = ⟨(s : ℝ) - 1, by constructor <;> linarith⟩ := by
        show Set.projIcc 0 1 zero_le_one ((s : ℝ) - 1) = _
        exact Set.projIcc_of_mem zero_le_one _
      rw [hrevs, hρ1]
      show γ.val A + AffineMap.lineMap (0 : Point) w ((s : ℝ) - 1) =
        (2 - (s : ℝ)) • γ.val A + ((s : ℝ) - 1) • γ.val B
      rw [AffineMap.lineMap_apply_module', hwdef]
      module
  -- additivity of the curve area along the cut at `s = 1`
  have hΓ2 : (0 : ℝ) ≤ 2 := by norm_num
  have hba : (0 : ℝ) < b - a := by linarith
  have hconcat : IsPathConcatenation (⟨0, 2, hΓ2, Γ⟩ : RectifiablePathData)
      ![(⟨a, b, hab.le, γrev⟩ : RectifiablePathData),
        ⟨0, 1, zero_le_one, lineSegmentBVPath (γ.val A) (γ.val B)⟩] := by
    refine ⟨by norm_num,
      ![⟨0, by norm_num⟩, ⟨1, by norm_num⟩, ⟨2, by norm_num⟩], ?_, ?_, ?_, ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;>
        first
          | rfl
          | (exact absurd hij (by decide))
          | (refine Subtype.mk_le_mk.mpr ?_; norm_num)
    · rfl
    · rfl
    · intro i
      fin_cases i
      · show ∃ (ϕ : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1)
            (ψ : Set.Icc (0 : ℝ) 1 → Set.Icc a b),
            Continuous ϕ ∧ Monotone ϕ ∧ Function.Surjective ϕ ∧
              Continuous ψ ∧ Monotone ψ ∧ Function.Surjective ψ ∧
              ∀ u, Γ.val ⟨(ϕ u : ℝ), (ϕ u).property.1,
                le_trans (ϕ u).property.2 (by norm_num)⟩ = γrev.val (ψ u)
        refine ⟨fun u ↦ ⟨(u : ℝ), u.property.1, u.property.2⟩,
          fun u ↦ ⟨a + (b - a) * (u : ℝ),
            by linarith only [mul_nonneg hba.le u.property.1],
            by linarith only [mul_le_mul_of_nonneg_left u.property.2 hba.le]⟩,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact continuous_subtype_val.subtype_mk _
        · exact fun x y hxy ↦ hxy
        · exact fun z ↦ ⟨⟨(z : ℝ), z.property.1, z.property.2⟩, Subtype.ext rfl⟩
        · exact (continuous_const.add
            (continuous_const.mul continuous_subtype_val)).subtype_mk _
        · intro x y hxy
          have hxy' : (x : ℝ) ≤ (y : ℝ) := hxy
          show a + (b - a) * (x : ℝ) ≤ a + (b - a) * (y : ℝ)
          linarith only [mul_le_mul_of_nonneg_left hxy' hba.le]
        · intro t
          refine ⟨⟨((t : ℝ) - a) / (b - a), ?_, ?_⟩, ?_⟩
          · exact div_nonneg (by linarith only [t.property.1]) hba.le
          · rw [div_le_one hba]
            linarith only [t.property.2]
          · apply Subtype.ext
            show a + (b - a) * (((t : ℝ) - a) / (b - a)) = (t : ℝ)
            field_simp
            ring
        · intro u
          have h0 : (0 : ℝ) ≤ (u : ℝ) := u.property.1
          have h1 : (u : ℝ) ≤ 1 := u.property.2
          rw [hΓval]
          show monotoneRoofLoop hab γ ⟨(u : ℝ), h0, by linarith⟩ =
            γ.val (Set.Icc.reverse hab.le ⟨a + (b - a) * (u : ℝ),
              by linarith only [mul_nonneg hba.le h0],
              by linarith only [mul_le_mul_of_nonneg_left h1 hba.le]⟩)
          unfold monotoneRoofLoop
          rw [dite_eq_left (show ((⟨(u : ℝ), h0, by linarith⟩ : Set.Icc (0 : ℝ) 2) : ℝ) ≤ 1
            from h1)]
          exact congrArg (fun t ↦ γ.val t) (Subtype.ext (by
            show b - (b - a) * (u : ℝ) = a + b - (a + (b - a) * (u : ℝ))
            ring))
      · show ∃ (ϕ : Set.Icc (0 : ℝ) 1 → Set.Icc (1 : ℝ) 2)
            (ψ : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1),
            Continuous ϕ ∧ Monotone ϕ ∧ Function.Surjective ϕ ∧
              Continuous ψ ∧ Monotone ψ ∧ Function.Surjective ψ ∧
              ∀ u, Γ.val ⟨(ϕ u : ℝ), le_trans (by norm_num) (ϕ u).property.1,
                (ϕ u).property.2⟩ =
                (lineSegmentBVPath (γ.val A) (γ.val B)).val (ψ u)
        refine ⟨fun u ↦ ⟨1 + (u : ℝ), by linarith [u.property.1], by
            linarith [u.property.2]⟩,
          fun u ↦ u, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact (continuous_const.add continuous_subtype_val).subtype_mk _
        · intro x y hxy
          have hxy' : (x : ℝ) ≤ (y : ℝ) := hxy
          show (1 : ℝ) + (x : ℝ) ≤ 1 + (y : ℝ)
          linarith
        · intro z
          refine ⟨⟨(z : ℝ) - 1, by linarith [z.property.1], by
            linarith [z.property.2]⟩, ?_⟩
          apply Subtype.ext
          show (1 : ℝ) + ((z : ℝ) - 1) = (z : ℝ)
          ring
        · exact continuous_id
        · exact fun x y hxy ↦ hxy
        · exact fun z ↦ ⟨z, rfl⟩
        · intro u
          have h0 : (0 : ℝ) ≤ (u : ℝ) := u.property.1
          have h1 : (u : ℝ) ≤ 1 := u.property.2
          rw [hΓval]
          show monotoneRoofLoop hab γ ⟨1 + (u : ℝ), by linarith, by linarith⟩ =
            Path.segment (γ.val A) (γ.val B) u
          unfold monotoneRoofLoop
          rcases eq_or_lt_of_le h0 with hu0 | hu0
          · rw [dite_eq_left (show ((⟨1 + (u : ℝ), by linarith, by linarith⟩ :
              Set.Icc (0 : ℝ) 2) : ℝ) ≤ 1 from by simp [← hu0])]
            have huval : (u : ℝ) = 0 := hu0.symm
            have hseg : Path.segment (γ.val A) (γ.val B) u = γ.val A := by
              rw [Path.segment_apply]
              rw [show (u : ℝ) = 0 from huval]
              simp
            rw [hseg]
            exact congrArg (fun t ↦ γ.val t) (Subtype.ext (by
              show b - (b - a) * (1 + (u : ℝ)) = a
              rw [huval]
              ring))
          · rw [dite_eq_right (show ¬ ((⟨1 + (u : ℝ), by linarith, by linarith⟩ :
              Set.Icc (0 : ℝ) 2) : ℝ) ≤ 1 from by
                show ¬ (1 + (u : ℝ) ≤ 1)
                linarith)]
            show (2 - (1 + (u : ℝ))) • γ.val A + ((1 + (u : ℝ)) - 1) • γ.val B =
              Path.segment (γ.val A) (γ.val B) u
            rw [Path.segment_apply, AffineMap.lineMap_apply_module']
            module
  -- the two pieces and the final assembly
  have hsum := curveArea_concatenation (⟨0, 2, hΓ2, Γ⟩ : RectifiablePathData)
    ![(⟨a, b, hab.le, γrev⟩ : RectifiablePathData),
      ⟨0, 1, zero_le_one, lineSegmentBVPath (γ.val A) (γ.val B)⟩] hconcat
  have hbase : curveAreaFunctional (lineSegmentBVPath (γ.val A) (γ.val B)) = 0 := by
    rw [curveAreaFunctional_lineSegmentBVPath, segmentArea, planeCrossProduct, ha, hb]
    ring
  have hJΓ : curveAreaFunctional Γ = intervalStieltjesIntegral K H.toFun Set.univ := by
    have hΓsum : curveAreaFunctional Γ =
        curveAreaFunctional γrev +
          curveAreaFunctional (lineSegmentBVPath (γ.val A) (γ.val B)) := by
      rw [show curveAreaFunctional Γ =
        curveAreaFunctional (⟨0, 2, hΓ2, Γ⟩ : RectifiablePathData).path from rfl, hsum,
        Fin.sum_univ_two]
      rfl
    rw [hΓsum, hbase, hJrev, hJγ]
    ring
  have hheightint : (∫ s in c..d, monotoneRoofHeight hab γ s) = ∫ s in c..d, g s := by
    apply intervalIntegral.integral_congr
    intro s hs
    exact hheight s (by rwa [Set.uIcc_of_le hcd.le] at hs)
  exact ⟨Γ, hΓval, by rw [hJΓ, hroofint, harea], harea.trans hheightint.symm⟩

/-- Above a parameter's abscissa, a strictly monotone roof has that parameter's ordinate. -/
theorem monotoneRoofHeight_apply {a b : ℝ} (hab : a < b) (γ : ContinuousBVPaths a b)
    (hk : StrictMono fun t ↦ γ.val t 0) (s : Set.Icc a b) :
    monotoneRoofHeight hab γ (γ.val s 0) = γ.val s 1 := by
  classical
  have hne : Nonempty (Set.Icc a b) := ⟨⟨a, le_rfl, hab.le⟩⟩
  have hinv : @Function.invFun _ _ hne (fun t ↦ γ.val t 0) (γ.val s 0) = s :=
    hk.injective (@Function.invFun_eq _ _ hne (fun t ↦ γ.val t 0) _ ⟨s, rfl⟩)
  show γ.val (@Function.invFun _ _ hne (fun t ↦ γ.val t 0) (γ.val s 0)) 1 = γ.val s 1
  rw [hinv]

/-- Every abscissa between a roof's endpoints is the abscissa of a roof parameter. -/
theorem exists_eq_monotoneRoof_fst {a b : ℝ} (hab : a < b) (γ : ContinuousBVPaths a b)
    {c : ℝ} (hc : c ∈ Set.Icc (γ.val ⟨a, le_rfl, hab.le⟩ 0) (γ.val ⟨b, hab.le, le_rfl⟩ 0)) :
    ∃ s : Set.Icc a b, γ.val s 0 = c := by
  have : PreconnectedSpace (Set.Icc a b) := Subtype.preconnectedSpace isPreconnected_Icc
  exact intermediate_value_univ _ _ ((PiLp.continuous_apply 2 _ 0).comp γ.property.1) hc

/-- The closed region under a strictly monotone roof, described parametrically: it consists of the
points on or below the roof on the vertical line through some roof parameter. -/
theorem monotoneRoofRegion_eq_param {a b : ℝ} (hab : a < b) (γ : ContinuousBVPaths a b)
    (hk : StrictMono fun t ↦ γ.val t 0) :
    monotoneRoofRegion hab γ =
      {p : Point | ∃ s : Set.Icc a b, p 0 = γ.val s 0 ∧ 0 ≤ p 1 ∧ p 1 ≤ γ.val s 1} := by
  ext p
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    obtain ⟨s, hs⟩ := exists_eq_monotoneRoof_fst hab γ ⟨h1, h2⟩
    refine ⟨s, hs.symm, h3, ?_⟩
    rwa [← hs, monotoneRoofHeight_apply hab γ hk s] at h4
  · rintro ⟨s, hs0, hs1, hs2⟩
    refine ⟨?_, ?_, hs1, ?_⟩
    · rw [hs0]
      exact hk.monotone (show (⟨a, le_rfl, hab.le⟩ : Set.Icc a b) ≤ s from s.property.1)
    · rw [hs0]
      exact hk.monotone (show s ≤ (⟨b, hab.le, le_rfl⟩ : Set.Icc a b) from s.property.2)
    · rw [hs0, monotoneRoofHeight_apply hab γ hk s]
      exact hs2

end MovingSofa
