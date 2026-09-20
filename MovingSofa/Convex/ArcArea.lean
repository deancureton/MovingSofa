import MovingSofa.Convex.ArcCutBoundary
import MovingSofa.Convex.Linearity
import MovingSofa.Curve.Jordan.SignedArea
import MovingSofa.Convex.ArcCutArea

noncomputable section

open MeasureTheory

namespace MovingSofa

def RealizesConvexArc (K : ConvexBody Point) (a b : ℝ)
    (Γ : RectifiableOrientedArc) : Prop :=
  Γ.val.carrier = convexBoundaryArc K a b ∧
    Γ.val.startPoint = (edgeVertices K (a : Real.Angle)).1 ∧
    Γ.val.endPoint = (edgeVertices K (b : Real.Angle)).2

def convexArcArea (K : ConvexBody Point) (a b : ℝ) : ℝ := by
  classical
  exact if h : ∃ Γ, RealizesConvexArc K a b Γ then jordanArcArea h.choose else 0

/-- Every realization of a convex boundary arc computes that arc's signed area. -/
theorem convexArcArea_eq_jordanArcArea_of_realizes {K : ConvexBody Point} {a b : ℝ}
    {Γ : RectifiableOrientedArc} (hΓ : RealizesConvexArc K a b Γ) :
    convexArcArea K a b = jordanArcArea Γ := by
  rw [convexArcArea, dite_eq_left ⟨Γ, hΓ⟩]
  let Δ := Classical.choose (show ∃ Γ, RealizesConvexArc K a b Γ from ⟨Γ, hΓ⟩)
  have hΔ : RealizesConvexArc K a b Δ :=
    Classical.choose_spec (show ∃ Γ, RealizesConvexArc K a b Γ from ⟨Γ, hΓ⟩)
  change curveAreaFunctional (Classical.choice Δ.property).path =
    curveAreaFunctional (Classical.choice Γ.property).path
  exact (curveArea_reparametrization.2.1 Δ Γ
    (Classical.choice Δ.property) (Classical.choice Γ.property)
    (hΔ.1.trans hΓ.1.symm)).1
      (hΔ.2.1.trans hΓ.2.1.symm) (hΔ.2.2.trans hΓ.2.2.symm)

/-- Any bounded-variation parametrization of a convex boundary arc computes that arc's signed
area. -/
theorem convexArcArea_eq_curveAreaFunctional_of_realizes {K : ConvexBody Point} {a b : ℝ}
    {Γ : OrientedJordanArc} (p : ArcBVParametrization Γ)
    (hΓ : RealizesConvexArc K a b ⟨Γ, ⟨p⟩⟩) :
    convexArcArea K a b = curveAreaFunctional p.path := by
  rw [convexArcArea_eq_jordanArcArea_of_realizes hΓ]
  exact (curveArea_arc_same_carrier Γ Γ
    (Classical.choice (⟨Γ, ⟨p⟩⟩ : RectifiableOrientedArc).property) p rfl).1 rfl rfl

/-- A continuous bounded-variation path on `[a, b]` that traces a convex boundary arc
injectively, from the arc's first vertex to its last, computes that arc's signed area. -/
theorem convexArcArea_eq_curveAreaFunctional_of_injOn {K : ConvexBody Point} {α β a b : ℝ}
    {f : ℝ → Point} (x : ContinuousBVPaths a b) (hab : a < b)
    (hx : ∀ t : Set.Icc a b, x.val t = f t) (hinj : Set.InjOn f (Set.Icc a b))
    (himage : f '' Set.Icc a b = convexBoundaryArc K α β)
    (hstart : f a = (edgeVertices K (α : Real.Angle)).1)
    (hend : f b = (edgeVertices K (β : Real.Angle)).2) :
    convexArcArea K α β = curveAreaFunctional x := by
  have hxinj : Function.Injective x.val := fun s t hst ↦
    Subtype.ext (hinj s.2 t.2 (by rw [← hx s, ← hx t, hst]))
  have hrange : Set.range x.val = convexBoundaryArc K α β := by
    rw [← himage, Set.image_eq_range]
    exact congrArg Set.range (funext hx)
  have hstart' : x.val ⟨a, le_rfl, hab.le⟩ = (edgeVertices K (α : Real.Angle)).1 := by
    rw [hx, hstart]
  have hend' : x.val ⟨b, hab.le, le_rfl⟩ = (edgeVertices K (β : Real.Angle)).2 := by
    rw [hx, hend]
  let Γ : OrientedJordanArc :=
    { carrier := convexBoundaryArc K α β
      startPoint := (edgeVertices K (α : Real.Angle)).1
      endPoint := (edgeVertices K (β : Real.Angle)).2
      parametrizable :=
        ⟨a, b, hab.le, x.val, x.property.1, hxinj, hrange, hstart', hend'⟩ }
  exact convexArcArea_eq_curveAreaFunctional_of_realizes (Γ := Γ)
    ⟨a, b, hab.le, x, hxinj, hrange, hstart', hend'⟩ ⟨rfl, rfl, rfl⟩

private theorem exists_degenerate_convexArc (K : ConvexBody Point) (a b : ℝ)
    (hab : a < b) (hba : b < a + Real.pi)
    (heq : (edgeVertices K (a : Real.Angle)).1 =
      (edgeVertices K (b : Real.Angle)).2) :
    ∃ Γ : RectifiableOrientedArc,
      RealizesConvexArc K a b Γ ∧ convexArcArea K a b = jordanArcArea Γ ∧
      (Γ.val.startPoint = Γ.val.endPoint → Γ.val.carrier = {Γ.val.startPoint}) := by
  let P := (edgeVertices K (a : Real.Angle)).1
  have hcut := (convexBoundaryArc_cut K a b hab hba P P (supportingIntersection K a b)
    rfl heq rfl).1 rfl
  obtain ⟨Γ, hcarrier, hstart, hend, _⟩ := (segmentArea_jordan_and_frame P P).1
  have hreal : RealizesConvexArc K a b Γ := by
    refine ⟨hcarrier.trans (segment_same ℝ P) |>.trans hcut.2.symm,
      hstart, hend.trans heq⟩
  exact ⟨Γ, hreal, convexArcArea_eq_jordanArcArea_of_realizes hreal, fun _ ↦ by
    rw [hcarrier, segment_same, hstart]⟩

private theorem surfaceAreaMeasure_openArc_eq_zero_of_convexBoundaryArc_eq_singleton
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    {P : Point} (hArc : convexBoundaryArc K a b = {P}) :
    surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b) = 0 := by
  let E := (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b
  have hmeas : MeasurableSet E := (Real.Angle.isOpen_image_Ioo a b).measurableSet
  have hsubset : E ⊆ (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Icc a b :=
    Set.image_mono Set.Ioo_subset_Icc_self
  rw [(surfaceAreaMeasure_face_union K).2.2.2.2 E hmeas
    (Or.inr ⟨a, b, hab.le, hba, hsubset⟩)]
  have hunion_sub : (⋃ t ∈ E, exposedEdge K t) ⊆ {P} := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨t, ht⟩ := hx
    obtain ⟨htE, hxt⟩ := ht
    obtain ⟨r, hr, rfl⟩ := htE
    have hxArc : x ∈ convexBoundaryArc K a b := by
      change x ∈ ({(edgeVertices K (a : Real.Angle)).1} ∪
        (⋃ t ∈ Set.Ioo a b, exposedEdge K (t : Real.Angle))) ∪
        {(edgeVertices K (b : Real.Angle)).2}
      apply Set.mem_union_left
      apply Set.mem_union_right
      exact Set.mem_iUnion.2 ⟨r, Set.mem_iUnion.2 ⟨hr, hxt⟩⟩
    rw [hArc] at hxArc
    exact hxArc
  have hunion_nonempty : (⋃ t ∈ E, exposedEdge K t).Nonempty := by
    let r := (a + b) / 2
    have hr : r ∈ Set.Ioo a b := by dsimp [r]; constructor <;> linarith
    obtain ⟨x, hx⟩ := exposedEdge_nonempty K (r : Real.Angle)
    exact ⟨x, Set.mem_iUnion.2 ⟨(r : Real.Angle), Set.mem_iUnion.2
      ⟨⟨r, hr, rfl⟩, hx⟩⟩⟩
  have hunion : (⋃ t ∈ E, exposedEdge K t) = {P} :=
    Set.Nonempty.subset_singleton_iff hunion_nonempty |>.mp hunion_sub
  rw [hunion]
  let _ := MeasureTheory.Measure.nullSingletonClass_hausdorff Point
    (by norm_num : (0 : ℝ) < 1)
  exact measure_singleton P

private theorem convexArcArea_eq_integral_of_endpoints_eq (K : ConvexBody Point)
    {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (heq : (edgeVertices K (a : Real.Angle)).1 =
      (edgeVertices K (b : Real.Angle)).2) :
    convexArcArea K a b =
      (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
        supportValue K t ∂surfaceAreaMeasure K) / 2 := by
  let P := (edgeVertices K (a : Real.Angle)).1
  have hcut := (convexBoundaryArc_cut K a b hab hba P P (supportingIntersection K a b)
    rfl heq rfl).1 rfl
  obtain ⟨Γ, hcarrier, hstart, hend, hΓarea⟩ := (segmentArea_jordan_and_frame P P).1
  have hreal : RealizesConvexArc K a b Γ := by
    refine ⟨hcarrier.trans (segment_same ℝ P) |>.trans hcut.2.symm,
      hstart, hend.trans heq⟩
  rw [convexArcArea_eq_jordanArcArea_of_realizes hreal, hΓarea]
  have hμ := surfaceAreaMeasure_openArc_eq_zero_of_convexBoundaryArc_eq_singleton
    K hab hba hcut.2
  rw [MeasureTheory.setIntegral_measure_zero _ hμ]
  simp [segmentArea, planeCrossProduct]
  ring

private theorem exists_pos_smul_tangentVector_of_cut
    (K : ConvexBody Point) {a t : ℝ} (hat : a < t) (hta : t < a + Real.pi)
    {P Q : Point} (hP : P = (edgeVertices K (a : Real.Angle)).1)
    (hQK : Q ∈ K) (hne : P ≠ Q)
    (hnormal : inner ℝ P (normalVector (t : Real.Angle)) =
      inner ℝ Q (normalVector (t : Real.Angle))) :
    ∃ d : ℝ, 0 < d ∧ Q - P = d • tangentVector (t : Real.Angle) := by
  let d := inner ℝ (Q - P) (tangentVector (t : Real.Angle))
  have hnormal0 : inner ℝ (Q - P) (normalVector (t : Real.Angle)) = 0 := by
    rw [inner_sub_left, hnormal, sub_self]
  have hdecomp : Q - P = d • tangentVector (t : Real.Angle) := by
    rw [← inner_normalVector_smul_add_inner_tangentVector_smul
      (Q - P) (t : Real.Angle), hnormal0, zero_smul, zero_add]
  have hPa : inner ℝ P (normalVector (a : Real.Angle)) = supportValue K a := by
    rw [hP]
    exact (edgeVertices_fst_mem K (a : Real.Angle)).2
  have hQa : inner ℝ Q (normalVector (a : Real.Angle)) ≤ supportValue K a :=
    inner_le_supportValue K hQK (a : Real.Angle)
  have hinner : inner ℝ (Q - P) (normalVector (a : Real.Angle)) ≤ 0 := by
    rw [inner_sub_left, hPa]
    linarith
  have hsin : 0 < Real.sin (t - a) := Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hat) (by linarith)
  have htana : inner ℝ (tangentVector (t : Real.Angle))
      (normalVector (a : Real.Angle)) = -Real.sin (t - a) := by
    rw [real_inner_comm]
    have h := sin_sub_eq_neg_inner_normalVector_tangentVector
      (a : Real.Angle) (t : Real.Angle)
    have h' : (((t - a : ℝ) : Real.Angle)).sin =
        -inner ℝ (normalVector (a : Real.Angle)) (tangentVector (t : Real.Angle)) := by
      simpa only [Real.Angle.coe_sub] using h
    rw [Real.Angle.sin_coe] at h'
    linarith
  have hdnonneg : 0 ≤ d := by
    rw [hdecomp, real_inner_smul_left, htana] at hinner
    nlinarith
  have hdne : d ≠ 0 := by
    intro hd
    apply hne
    have : Q - P = 0 := by rw [hdecomp, hd, zero_smul]
    exact (sub_eq_zero.mp this).symm
  exact ⟨d, lt_of_le_of_ne hdnonneg (Ne.symm hdne), hdecomp⟩

/-- The half support integral against a surface measure is convex-bilinear in the pair of
bodies, by convex-linearity of support functions and surface measures. -/
theorem convexArcIntegral_bilinear (a b : ℝ) :
    IsConvexBilinear convexBodyCombination convexBodyCombination realCombination
      (fun K L : ConvexBody Point ↦ (1 / 2 : ℝ) *
        ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
          supportValue K t ∂surfaceAreaMeasure L) := by
  let E := (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b
  have hcont (K : ConvexBody Point) : Continuous (fun u : Real.Angle ↦ supportValue K u) :=
    (compactSet_support_continuity K K K.nonempty K.isCompact K.nonempty K.isCompact).2.2.1
  have hint (K L : ConvexBody Point) :
      Integrable (fun u : Real.Angle ↦ supportValue K u) (surfaceAreaMeasure L) := by
    let _ : IsFiniteMeasure (surfaceAreaMeasure L) := (surfaceAreaMeasure_face_union L).1
    exact (hcont K).integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _))
  constructor
  · intro K t L M
    have hmeasure := (convexBody_maps_linear t L M).2.2.2
    change (1 / 2 : ℝ) * (∫ u in E, supportValue K u ∂surfaceAreaMeasure
        (convexBodyCombination t L M)) = _
    simp only [realCombination]
    rw [hmeasure, Measure.restrict_add, Measure.restrict_smul, Measure.restrict_smul,
      integral_add_measure ((hint K L).restrict.smul_measure _)
        ((hint K M).restrict.smul_measure _)]
    simp only [integral_smul_measure, ENNReal.toReal_ofReal,
      sub_nonneg.mpr (show (t : ℝ) ≤ 1 from t.property.2), t.property.1]
    ring
    all_goals exact ENNReal.ofReal_ne_top
  · intro L t K M
    change (1 / 2 : ℝ) * (∫ u in E, supportValue (convexBodyCombination t K M) u
      ∂surfaceAreaMeasure L) = _
    simp only [realCombination]
    have hfun : (fun u : Real.Angle ↦ supportValue (convexBodyCombination t K M) u) =
        fun u ↦ (1 - (t : ℝ)) * supportValue K u + (t : ℝ) * supportValue M u := by
      funext u
      exact (convexBody_maps_linear t K M).1 u
    rw [hfun, integral_add ((hint K L).restrict.const_mul _) ((hint M L).restrict.const_mul _),
      integral_const_mul, integral_const_mul]
    ring

private theorem convexArcArea_quadratic_of_integral_eq (a b : ℝ)
    (harea : ∀ K : ConvexBody Point, convexArcArea K a b =
      (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
        supportValue K t ∂surfaceAreaMeasure K) / 2) :
    IsQuadraticFunctional convexBodyCombination (fun K ↦ convexArcArea K a b) := by
  let B := fun K L : ConvexBody Point ↦ (1 / 2 : ℝ) *
    ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
      supportValue K t ∂surfaceAreaMeasure L
  refine ⟨B, convexArcIntegral_bilinear a b, ?_⟩
  intro K
  change convexArcArea K a b = B K K
  rw [harea K]
  simp only [B]
  ring

private theorem convexArc_area_of_realization_and_integral
    (a b : ℝ)
    (hgeom : ∀ K : ConvexBody Point,
      ∃ Γ : RectifiableOrientedArc,
        RealizesConvexArc K a b Γ ∧
        (Γ.val.startPoint = Γ.val.endPoint → Γ.val.carrier = {Γ.val.startPoint}))
    (harea : ∀ K : ConvexBody Point, convexArcArea K a b =
      (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
        supportValue K t ∂surfaceAreaMeasure K) / 2) :
    (∀ K : ConvexBody Point, ∃ Γ : RectifiableOrientedArc,
      RealizesConvexArc K a b Γ ∧ convexArcArea K a b = jordanArcArea Γ ∧
      (Γ.val.startPoint = Γ.val.endPoint → Γ.val.carrier = {Γ.val.startPoint})) ∧
    (∀ K : ConvexBody Point, convexArcArea K a b =
      (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
        supportValue K t ∂surfaceAreaMeasure K) / 2) ∧
    IsQuadraticFunctional convexBodyCombination (fun K ↦ convexArcArea K a b) := by
  refine ⟨?_, harea, convexArcArea_quadratic_of_integral_eq a b harea⟩
  intro K
  obtain ⟨Γ, hreal, hsingleton⟩ := hgeom K
  exact ⟨Γ, hreal, convexArcArea_eq_jordanArcArea_of_realizes hreal, hsingleton⟩

private theorem exists_convexArc_realization (a b : ℝ) (hab : a < b)
    (hba : b < a + Real.pi) (K : ConvexBody Point) :
    ∃ Γ : RectifiableOrientedArc,
      RealizesConvexArc K a b Γ ∧
      (Γ.val.startPoint = Γ.val.endPoint → Γ.val.carrier = {Γ.val.startPoint}) := by
  by_cases heq : (edgeVertices K (a : Real.Angle)).1 =
      (edgeVertices K (b : Real.Angle)).2
  · obtain ⟨Γ, hreal, -, hsingleton⟩ := exists_degenerate_convexArc K a b hab hba heq
    exact ⟨Γ, hreal, hsingleton⟩
  · let P := (edgeVertices K (a : Real.Angle)).1
    let Q := (edgeVertices K (b : Real.Angle)).2
    let O := supportingIntersection K a b
    obtain ⟨-, hcut⟩ := convexBoundaryArc_cut K a b hab hba P Q O rfl rfl rfl
    obtain ⟨hncol, t, c, K', hat, htb, hPt, hQt, hcO, hK', hleft, hmiddle,
      hright, hterminal⟩ := hcut heq
    by_cases hInt : (interior (K' : Set Point)).Nonempty
    · obtain ⟨Γ, hcarrier, hstart, hend⟩ :=
        exists_rectifiableOrientedArc_convexBoundaryArc_of_cut K K' a b t c P Q
          hat htb hba heq hPt hQt rfl rfl hleft hmiddle hright hterminal hInt
      have hreal : RealizesConvexArc K a b Γ := ⟨hcarrier, hstart, hend⟩
      refine ⟨Γ, hreal, ?_⟩
      intro hendpoints
      exact (heq (hstart.symm.trans (hendpoints.trans hend))) |>.elim
    · have hInt' : interior (K' : Set Point) = ∅ := Set.not_nonempty_iff_eq_empty.mp hInt
      have harc := convexBoundaryArc_eq_segment_of_cut_interior_empty K K' a b t c P Q
        hat htb hba heq hPt hQt rfl rfl hleft hmiddle hright hInt'
      obtain ⟨Γ, hcarrier, hstart, hend, -⟩ := (segmentArea_jordan_and_frame P Q).1
      have hreal : RealizesConvexArc K a b Γ :=
        ⟨hcarrier.trans harc.symm, hstart, hend⟩
      refine ⟨Γ, hreal, ?_⟩
      intro hendpoints
      exact (heq (hstart.symm.trans (hendpoints.trans hend))) |>.elim

private theorem surfaceAreaMeasure_restrict_openArc_eq_of_exposedEdge_eq
    (K L : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (hfaces : ∀ s ∈ Set.Ioo a b,
      exposedEdge K (s : Real.Angle) = exposedEdge L (s : Real.Angle)) :
    (surfaceAreaMeasure K).restrict
        ((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b) =
      (surfaceAreaMeasure L).restrict
        ((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b) := by
  let E := (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b
  have hE : MeasurableSet E := Real.Angle.isOpen_image_Ioo a b |>.measurableSet
  apply Measure.ext
  intro S hS
  rw [Measure.restrict_apply hS, Measure.restrict_apply hS]
  have hSE : MeasurableSet (S ∩ E) := hS.inter hE
  have hdomain : S ∩ E ⊆ (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Icc a b :=
    Set.inter_subset_right.trans (Set.image_mono Set.Ioo_subset_Icc_self)
  rw [(surfaceAreaMeasure_face_union K).2.2.2.2 (S ∩ E) hSE
      (Or.inr ⟨a, b, hab.le, hba, hdomain⟩),
    (surfaceAreaMeasure_face_union L).2.2.2.2 (S ∩ E) hSE
      (Or.inr ⟨a, b, hab.le, hba, hdomain⟩)]
  congr 2
  ext p
  simp only [Set.mem_iUnion, Set.mem_inter_iff, E]
  constructor
  · rintro ⟨⟨hpS, s, hs, hsp⟩, hx⟩
    subst p
    exact ⟨⟨hpS, ⟨s, hs, rfl⟩⟩, hfaces s hs ▸ hx⟩
  · rintro ⟨⟨hpS, s, hs, hsp⟩, hx⟩
    subst p
    exact ⟨⟨hpS, ⟨s, hs, rfl⟩⟩, hfaces s hs |>.symm ▸ hx⟩

private theorem surfaceAreaMeasure_compl_openArc_union_terminal_eq_zero_of_cut
    (K : ConvexBody Point) {a b t : ℝ} {P Q : Point}
    (hleft : ∀ s ∈ Set.Ioc (t - Real.pi) a, exposedEdge K s = {P})
    (hright : ∀ s ∈ Set.Ico b (t + Real.pi), exposedEdge K s = {Q})
    (hInt : (interior (K : Set Point)).Nonempty) :
    surfaceAreaMeasure K
      (((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b ∪
        {((t + Real.pi : ℝ) : Real.Angle)})ᶜ) = 0 := by
  let E := (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b
  let θ : Real.Angle := (t + Real.pi : ℝ)
  let D := (E ∪ {θ})ᶜ
  have hD : MeasurableSet D :=
    ((Real.Angle.isOpen_image_Ioo a b).measurableSet.union
      (measurableSet_singleton θ)).compl
  have hface := (surfaceAreaMeasure_face_union K).2.2.2.2 D hD (Or.inl hInt)
  have hunion : (⋃ u ∈ D, exposedEdge K u) ⊆ {P, Q} := by
    intro x hx
    obtain ⟨u, huD, hxu⟩ := Set.mem_iUnion₂.mp hx
    let _ : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
    let s := AddCircle.equivIoc (2 * Real.pi) (t - Real.pi) u
    have hs : (s : ℝ) ∈ Set.Ioc (t - Real.pi) (t + Real.pi) := by
      have hs' := s.property
      convert hs' using 1
      ring_nf
    have hsu : (((s : ℝ) : Real.Angle)) = u := AddCircle.coe_equivIoc
    have hxs : x ∈ exposedEdge K (s : ℝ) := by simpa [hsu] using hxu
    rcases le_or_gt (s : ℝ) a with hsa | has
    · rw [hleft (s : ℝ) ⟨hs.1, hsa⟩] at hxs
      exact Or.inl (by simpa using hxs)
    · rcases lt_or_ge (s : ℝ) b with hsb | hbs
      · exfalso
        apply huD
        apply Set.mem_union_left
        exact ⟨s, ⟨has, hsb⟩, hsu⟩
      · rcases lt_or_eq_of_le hs.2 with hst | hst
        · rw [hright (s : ℝ) ⟨hbs, hst⟩] at hxs
          exact Or.inr (by simpa using hxs)
        · exfalso
          apply huD
          apply Set.mem_union_right
          simp only [Set.mem_singleton_iff, θ]
          rw [← hsu, hst]
  rw [show (((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b ∪
      {((t + Real.pi : ℝ) : Real.Angle)})ᶜ) = D by rfl, hface]
  let _ := Measure.nullSingletonClass_hausdorff Point (by norm_num : (0 : ℝ) < 1)
  exact measure_mono_null hunion
    ((Set.toFinite {P, Q}).measure_zero (Measure.hausdorffMeasure 1))

private theorem integral_eq_openArc_add_terminal_of_cut
    (K : ConvexBody Point) {a b t : ℝ} {P Q : Point}
    (hat : a < t) (htb : t < b) (hba : b < a + Real.pi)
    (hleft : ∀ s ∈ Set.Ioc (t - Real.pi) a, exposedEdge K s = {P})
    (hright : ∀ s ∈ Set.Ico b (t + Real.pi), exposedEdge K s = {Q})
    (hInt : (interior (K : Set Point)).Nonempty) :
    (∫ u, supportValue K u ∂surfaceAreaMeasure K) =
      (∫ u in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
        supportValue K u ∂surfaceAreaMeasure K) +
      (surfaceAreaMeasure K).real {((t + Real.pi : ℝ) : Real.Angle)} *
        supportValue K ((t + Real.pi : ℝ) : Real.Angle) := by
  let E := (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b
  let θ : Real.Angle := (t + Real.pi : ℝ)
  let C := E ∪ {θ}
  let _ : IsFiniteMeasure (surfaceAreaMeasure K) := (surfaceAreaMeasure_face_union K).1
  have hcont : Continuous (fun u : Real.Angle ↦ supportValue K u) :=
    (compactSet_support_continuity K K K.nonempty K.isCompact K.nonempty K.isCompact).2.2.1
  have hint : Integrable (fun u : Real.Angle ↦ supportValue K u) (surfaceAreaMeasure K) :=
    hcont.integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _))
  have hC : MeasurableSet C :=
    (Real.Angle.isOpen_image_Ioo a b).measurableSet.union (measurableSet_singleton θ)
  have hzero : surfaceAreaMeasure K Cᶜ = 0 := by
    exact surfaceAreaMeasure_compl_openArc_union_terminal_eq_zero_of_cut
      K hleft hright hInt
  have hdisj : Disjoint E {θ} := by
    rw [Set.disjoint_singleton_right]
    rintro ⟨s, hs, heq⟩
    have hlow : t - Real.pi < a := by linarith
    have hupp : b < t + Real.pi := by linarith
    have hsrange : s ∈ Set.Ioc (t - Real.pi) (t + Real.pi) :=
      ⟨hlow.trans hs.1, (hs.2.trans hupp).le⟩
    have htrange : t + Real.pi ∈ Set.Ioc (t - Real.pi) (t + Real.pi) :=
      ⟨by linarith [Real.pi_pos], le_rfl⟩
    have hinj := Real.Angle.injOn_coe_Ioc (by linarith [Real.pi_pos]) hsrange htrange heq
    rw [hinj] at hs
    exact (not_lt_of_ge hupp.le hs.2)
  have hsplit := MeasureTheory.setIntegral_union hdisj (measurableSet_singleton θ)
    hint.integrableOn hint.integrableOn
  have hall := MeasureTheory.integral_add_compl hC hint
  rw [MeasureTheory.setIntegral_measure_zero _ hzero, add_zero] at hall
  rw [← hall, hsplit, MeasureTheory.integral_singleton]
  rfl

private theorem terminal_surface_term_eq_segmentArea_of_cut
    (K : ConvexBody Point) {t c d : ℝ} {P Q : Point}
    (hPt : inner ℝ P (normalVector (t : Real.Angle)) = c)
    (hQt : inner ℝ Q (normalVector (t : Real.Angle)) = c)
    (hterminal : exposedEdge K (t + Real.pi) = segment ℝ Q P)
    (hd : 0 < d) (hdir : Q - P = d • tangentVector (t : Real.Angle)) :
    (surfaceAreaMeasure K).real {((t + Real.pi : ℝ) : Real.Angle)} *
        supportValue K ((t + Real.pi : ℝ) : Real.Angle) / 2 =
      segmentArea Q P := by
  let θ : Real.Angle := (t + Real.pi : ℝ)
  have hterminal' : exposedEdge K θ = segment ℝ Q P := by
    simpa only [θ, Real.Angle.coe_add] using hterminal
  have hmass : (surfaceAreaMeasure K).real {θ} = d := by
    have htangent_norm : ‖tangentVector (t : Real.Angle)‖ = 1 := by
      have hsq : ‖tangentVector (t : Real.Angle)‖ ^ 2 = 1 := by
        rw [← real_inner_self_eq_norm_sq, inner_tangentVector_self]
      nlinarith [norm_nonneg (tangentVector (t : Real.Angle))]
    rw [Measure.real, (surfaceAreaMeasure_atom_length K θ).1, hterminal',
      MeasureTheory.hausdorffMeasure_segment, edist_dist]
    simp only [dist_eq_norm, sub_eq_add_neg]
    rw [show Q + -P = Q - P by rfl, hdir, norm_smul, htangent_norm,
      mul_one, Real.norm_eq_abs, abs_of_pos hd]
    exact ENNReal.toReal_ofReal hd.le
  have hsupp : supportValue K θ = -c := by
    have hPterm : P ∈ exposedEdge K θ := by
      rw [hterminal']
      exact right_mem_segment ℝ Q P
    have h := hPterm.2
    change inner ℝ P (normalVector θ) = supportValue K θ at h
    change inner ℝ P (normalVector (((t + Real.pi : ℝ) : Real.Angle))) = _ at h
    rw [normalVector_add_pi, inner_neg_right, hPt] at h
    linarith
  have hQline : Q ∈ normalLine θ (-c) := by
    change inner ℝ Q (normalVector θ) = -c
    change inner ℝ Q (normalVector (((t + Real.pi : ℝ) : Real.Angle))) = -c
    rw [normalVector_add_pi, inner_neg_right, hQt]
  have hPline : P ∈ normalLine θ (-c) := by
    change inner ℝ P (normalVector θ) = -c
    change inner ℝ P (normalVector (((t + Real.pi : ℝ) : Real.Angle))) = -c
    rw [normalVector_add_pi, inner_neg_right, hPt]
  have hdir' : P - Q = d • tangentVector θ := by
    have htangent : tangentVector θ = -tangentVector (t : Real.Angle) := by
      ext i
      fin_cases i <;> simp [θ, tangentVector, frame]
    calc
      P - Q = -(Q - P) := by module
      _ = -(d • tangentVector (t : Real.Angle)) := congrArg Neg.neg hdir
      _ = d • tangentVector θ := by rw [htangent]; module
  rw [hmass, hsupp]
  rw [mul_comm]
  exact ((segmentArea_jordan_and_frame Q P).2 θ (-c) d hQline hPline hdir').symm

private theorem supportValue_eq_of_exposedEdge_eq (K L : ConvexBody Point)
    (t : Real.Angle) (hface : exposedEdge K t = exposedEdge L t) :
    supportValue K t = supportValue L t := by
  obtain ⟨p, hp⟩ := exposedEdge_nonempty K t
  have hp' : p ∈ exposedEdge L t := hface ▸ hp
  exact hp.2.symm.trans hp'.2

private theorem integral_openArc_eq_of_exposedEdge_eq
    (K L : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (hfaces : ∀ s ∈ Set.Ioo a b,
      exposedEdge K (s : Real.Angle) = exposedEdge L (s : Real.Angle)) :
    (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
        supportValue K t ∂surfaceAreaMeasure K) =
      ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
        supportValue L t ∂surfaceAreaMeasure L := by
  let E := (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b
  have hμ := surfaceAreaMeasure_restrict_openArc_eq_of_exposedEdge_eq
    K L hab hba hfaces
  change (∫ t, supportValue K t ∂(surfaceAreaMeasure K).restrict E) =
    ∫ t, supportValue L t ∂(surfaceAreaMeasure L).restrict E
  rw [hμ]
  apply MeasureTheory.integral_congr_ae
  have hE : MeasurableSet E := Real.Angle.isOpen_image_Ioo a b |>.measurableSet
  filter_upwards [ae_restrict_mem hE] with t ht
  obtain ⟨s, hs, rfl⟩ := ht
  exact supportValue_eq_of_exposedEdge_eq K L _ (hfaces s hs)

private theorem jordanArcArea_eq_integral_of_cut_interior_nonempty
    (K : ConvexBody Point) {a b t c d α β : ℝ} {P Q : Point}
    {x : ContinuousBVPaths α β} {A : RectifiableOrientedArc}
    (hαβ : α < β)
    (hx : IsOrientedJordanParametrization hαβ.le (frontier (K : Set Point)) true x.val)
    (hAarea : curveAreaFunctional x = jordanArcArea A + segmentArea Q P)
    (hat : a < t) (htb : t < b) (hba : b < a + Real.pi)
    (hPt : inner ℝ P (normalVector (t : Real.Angle)) = c)
    (hQt : inner ℝ Q (normalVector (t : Real.Angle)) = c)
    (hleft : ∀ s ∈ Set.Ioc (t - Real.pi) a, exposedEdge K s = {P})
    (hright : ∀ s ∈ Set.Ico b (t + Real.pi), exposedEdge K s = {Q})
    (hterminal : exposedEdge K (t + Real.pi) = segment ℝ Q P)
    (hInt : (interior (K : Set Point)).Nonempty)
    (hd : 0 < d) (hdir : Q - P = d • tangentVector (t : Real.Angle)) :
    jordanArcArea A =
      (∫ u in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
        supportValue K u ∂surfaceAreaMeasure K) / 2 := by
  have hxarea := curveArea_eq_jordanInterior_area α β hαβ.le
    (frontier (K : Set Point)) x hx
  rw [jordanInterior_frontier_eq_interior K.convex K.isCompact.isClosed
    K.isCompact.isBounded K.nonempty] at hxarea
  have hinterarea : ClassicalResults.area (interior (K : Set Point)) =
      ClassicalResults.area (K : Set Point) := by
    simp only [ClassicalResults.area]
    rw [measure_interior_of_null_frontier (K.convex.addHaar_frontier volume)]
  rw [hinterarea, (convexBody_area_support_integral.1 K)] at hxarea
  have hsplit := integral_eq_openArc_add_terminal_of_cut K hat htb hba hleft hright hInt
  have hterminalArea := terminal_surface_term_eq_segmentArea_of_cut K hPt hQt hterminal
    hd hdir
  rw [hAarea, hsplit] at hxarea
  linarith

private theorem convexArcArea_eq_integral_of_cut_interior_nonempty
    (K K' : ConvexBody Point) {a b t c d α β : ℝ} {P Q : Point}
    {x : ContinuousBVPaths α β} {A : RectifiableOrientedArc}
    (hαβ : α < β)
    (hx : IsOrientedJordanParametrization hαβ.le (frontier (K' : Set Point)) true x.val)
    (hAcarrier : A.val.carrier = convexBoundaryArc K a b)
    (hAstart : A.val.startPoint = P) (hAend : A.val.endPoint = Q)
    (hAarea : curveAreaFunctional x = jordanArcArea A + segmentArea Q P)
    (hP : P = (edgeVertices K (a : Real.Angle)).1)
    (hQ : Q = (edgeVertices K (b : Real.Angle)).2)
    (hat : a < t) (htb : t < b) (hba : b < a + Real.pi)
    (hPt : inner ℝ P (normalVector (t : Real.Angle)) = c)
    (hQt : inner ℝ Q (normalVector (t : Real.Angle)) = c)
    (hmiddle : ∀ s ∈ Set.Ioo a b, exposedEdge K' s = exposedEdge K s)
    (hleft : ∀ s ∈ Set.Ioc (t - Real.pi) a, exposedEdge K' s = {P})
    (hright : ∀ s ∈ Set.Ico b (t + Real.pi), exposedEdge K' s = {Q})
    (hterminal : exposedEdge K' (t + Real.pi) = segment ℝ Q P)
    (hInt : (interior (K' : Set Point)).Nonempty)
    (hd : 0 < d) (hdir : Q - P = d • tangentVector (t : Real.Angle)) :
    convexArcArea K a b =
      (∫ u in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
        supportValue K u ∂surfaceAreaMeasure K) / 2 := by
  have hreal : RealizesConvexArc K a b A := ⟨hAcarrier, hAstart.trans hP, hAend.trans hQ⟩
  rw [convexArcArea_eq_jordanArcArea_of_realizes hreal]
  rw [jordanArcArea_eq_integral_of_cut_interior_nonempty K' hαβ hx hAarea
    hat htb hba hPt hQt hleft hright hterminal hInt hd hdir]
  exact congrArg (fun z : ℝ ↦ z / 2)
    (integral_openArc_eq_of_exposedEdge_eq K' K (hat.trans htb) hba hmiddle)

private theorem integral_openArc_eq_segmentArea_of_segment
    (K : ConvexBody Point) {a b t c d : ℝ} {P Q : Point}
    (hat : a < t) (htb : t < b) (hba : b < a + Real.pi)
    (hK : (K : Set Point) = segment ℝ P Q) (hPQ : P ≠ Q)
    (hPt : inner ℝ P (normalVector (t : Real.Angle)) = c)
    (hQt : inner ℝ Q (normalVector (t : Real.Angle)) = c)
    (hd : 0 < d) (hdir : Q - P = d • tangentVector (t : Real.Angle)) :
    (∫ u in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
      supportValue K u ∂surfaceAreaMeasure K) / 2 = segmentArea P Q := by
  let E := (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b
  let θ : Real.Angle := (t : ℝ)
  have horth : inner ℝ (Q - P) (normalVector θ) = 0 := by
    change inner ℝ (Q - P) (normalVector (t : Real.Angle)) = 0
    rw [inner_sub_left, hQt, hPt, sub_self]
  have hpres : IsSegmentPresentation K (P, Q, θ) := ⟨hPQ, hK, horth⟩
  have htangent_norm : ‖tangentVector (t : Real.Angle)‖ = 1 := by
    have hsq : ‖tangentVector (t : Real.Angle)‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq, inner_tangentVector_self]
    nlinarith [norm_nonneg (tangentVector (t : Real.Angle))]
  have hdist : dist P Q = d := by
    rw [dist_eq_norm, show P - Q = -(Q - P) by module, norm_neg, hdir,
      norm_smul, htangent_norm, mul_one, Real.norm_eq_abs, abs_of_pos hd]
  have hE : MeasurableSet E := Real.Angle.isOpen_image_Ioo a b |>.measurableSet
  have htE : θ ∈ E := ⟨t, ⟨hat, htb⟩, rfl⟩
  have hopp : θ + (Real.pi : Real.Angle) ∉ E := by
    rintro ⟨s, hs, heq⟩
    have hsupper : s ≤ a + 2 * Real.pi := by
      have : s < a + Real.pi := hs.2.trans hba
      linarith [Real.pi_pos]
    have htupper : t + Real.pi ≤ a + 2 * Real.pi := by
      linarith [htb, hba, Real.pi_pos]
    have hsrange : s ∈ Set.Ioc a (a + 2 * Real.pi) := ⟨hs.1, hsupper⟩
    have htrange : t + Real.pi ∈ Set.Ioc a (a + 2 * Real.pi) :=
      ⟨by linarith [hat, Real.pi_pos], htupper⟩
    have hinj := Real.Angle.injOn_coe_Ioc (by linarith [Real.pi_pos])
      hsrange htrange
    have hst : s = t + Real.pi := hinj (by
      change (s : Real.Angle) = ((t + Real.pi : ℝ) : Real.Angle)
      simpa only [θ, Real.Angle.coe_add] using heq)
    linarith [hs.2, hba]
  have hmeasure : (surfaceAreaMeasure K).restrict E =
      ENNReal.ofReal d • Measure.dirac θ := by
    classical
    rw [surfaceAreaMeasure_eq_segmentPresentation K (P, Q, θ) hpres, hdist,
      Measure.restrict_smul, Measure.restrict_add]
    simp [restrict_dirac, htE, hopp]
  change (∫ u, supportValue K u ∂(surfaceAreaMeasure K).restrict E) / 2 = _
  rw [hmeasure, MeasureTheory.integral_smul_measure, MeasureTheory.integral_dirac,
    ENNReal.toReal_ofReal hd.le]
  have hPline : P ∈ normalLine θ c := hPt
  have hQline : Q ∈ normalLine θ c := hQt
  have hsupp : supportValue K θ = c := by
    have hpK : P ∈ K := by
      change P ∈ (K : Set Point)
      rw [hK]
      exact left_mem_segment ℝ P Q
    have hp : P ∈ exposedEdge K θ := by
      rw [exposedEdge_eq_segment_of_orthogonal K (P, Q, θ) hpres θ horth]
      exact hpK
    have hpEq := hp.2
    change inner ℝ P (normalVector θ) = supportValue K θ at hpEq
    exact hpEq.symm.trans hPt
  rw [hsupp]
  simp only [smul_eq_mul]
  convert ((segmentArea_jordan_and_frame P Q).2 θ c d hPline hQline hdir).symm using 1
  ring

private theorem convexArcArea_eq_integral_of_cut_interior_empty
    (K K' : ConvexBody Point) {a b t c d : ℝ} {P Q : Point}
    (hat : a < t) (htb : t < b) (hba : b < a + Real.pi)
    (hPQ : P ≠ Q)
    (hPt : inner ℝ P (normalVector (t : Real.Angle)) = c)
    (hQt : inner ℝ Q (normalVector (t : Real.Angle)) = c)
    (hP : P = (edgeVertices K (a : Real.Angle)).1)
    (hQ : Q = (edgeVertices K (b : Real.Angle)).2)
    (hleft : ∀ s ∈ Set.Ioc (t - Real.pi) a, exposedEdge K' s = {P})
    (hmiddle : ∀ s ∈ Set.Ioo a b, exposedEdge K' s = exposedEdge K s)
    (hright : ∀ s ∈ Set.Ico b (t + Real.pi), exposedEdge K' s = {Q})
    (hInt : interior (K' : Set Point) = ∅)
    (hd : 0 < d) (hdir : Q - P = d • tangentVector (t : Real.Angle)) :
    convexArcArea K a b =
      (∫ u in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
        supportValue K u ∂surfaceAreaMeasure K) / 2 := by
  have hPmem : P ∈ (K' : Set Point) := by
    have : P ∈ exposedEdge K' (a : Real.Angle) := by
      rw [hleft a ⟨by linarith [Real.pi_pos], le_rfl⟩]
      simp
    exact this.1
  have hQmem : Q ∈ (K' : Set Point) := by
    have : Q ∈ exposedEdge K' (b : Real.Angle) := by
      rw [hright b ⟨le_rfl, by linarith [Real.pi_pos]⟩]
      simp
    exact this.1
  have hnsub : ¬(K' : Set Point).Subsingleton := by
    intro hs
    exact hPQ (hs hPmem hQmem)
  obtain ⟨x, y, hxy, hK'⟩ := K'.exists_eq_segment_of_interior_empty hnsub hInt
  have hxP : x = P ∨ y = P := endpoint_of_exposedEdge_eq_singleton_of_eq_segment
    K' x y P (a : Real.Angle) hK' (hleft a ⟨by linarith [Real.pi_pos], le_rfl⟩)
  have hxQ : x = Q ∨ y = Q := endpoint_of_exposedEdge_eq_singleton_of_eq_segment
    K' x y Q (b : Real.Angle) hK' (hright b ⟨le_rfl, by linarith [Real.pi_pos]⟩)
  have hK'PQ : (K' : Set Point) = segment ℝ P Q := by
    rcases hxP with rfl | rfl <;> rcases hxQ with hxQ | hxQ
    · exact (hPQ hxQ).elim
    · simpa [hxQ] using hK'
    · simpa [hxQ, segment_symm ℝ] using hK'
    · exact (hPQ hxQ).elim
  have harc := convexBoundaryArc_eq_segment_of_cut_interior_empty K K' a b t c P Q
    hat htb hba hPQ hPt hQt hP hQ hleft hmiddle hright hInt
  obtain ⟨A, hAcarrier, hAstart, hAend, hAarea⟩ :=
    (segmentArea_jordan_and_frame P Q).1
  have hreal : RealizesConvexArc K a b A :=
    ⟨hAcarrier.trans harc.symm, hAstart.trans hP, hAend.trans hQ⟩
  rw [convexArcArea_eq_jordanArcArea_of_realizes hreal]
  rw [hAarea]
  rw [← integral_openArc_eq_segmentArea_of_segment K' hat htb hba hK'PQ hPQ
    hPt hQt hd hdir]
  exact congrArg (fun z : ℝ ↦ z / 2)
    (integral_openArc_eq_of_exposedEdge_eq K' K (hat.trans htb) hba hmiddle)

private theorem convexArcArea_eq_integral_of_endpoints_ne
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (hne : (edgeVertices K (a : Real.Angle)).1 ≠
      (edgeVertices K (b : Real.Angle)).2) :
    convexArcArea K a b =
      (∫ u in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
        supportValue K u ∂surfaceAreaMeasure K) / 2 := by
  let P := (edgeVertices K (a : Real.Angle)).1
  let Q := (edgeVertices K (b : Real.Angle)).2
  let O := supportingIntersection K a b
  obtain ⟨-, hcut⟩ := convexBoundaryArc_cut K a b hab hba P Q O rfl rfl rfl
  obtain ⟨hncol, t, c, K', hat, htb, hPt, hQt, hcO, hK', hleft, hmiddle,
    hright, hterminal⟩ := hcut hne
  have hnormal : inner ℝ P (normalVector (t : Real.Angle)) =
      inner ℝ Q (normalVector (t : Real.Angle)) := hPt.trans hQt.symm
  obtain ⟨d, hd, hdir⟩ := exists_pos_smul_tangentVector_of_cut K hat
    (htb.trans hba) rfl (edgeVertices_snd_mem K (b : Real.Angle)).1 hne hnormal
  by_cases hInt : (interior (K' : Set Point)).Nonempty
  · have hfrontier := frontier_eq_convexBoundaryArc_union_segment_of_cut
      K K' a b t P Q hat htb hba rfl rfl hleft hmiddle hright hterminal hInt
    have hinter := convexBoundaryArc_inter_segment_eq_endpoints_of_cut
      K K' a b t c P Q hat htb hba hne hPt hQt rfl rfl hleft hmiddle hright
        hterminal hInt
    obtain ⟨α, β, x, hαβ, hx, hbase⟩ :=
      exists_closedBVJordan_frontier_base_not_mem_chord K' t P Q hInt hterminal
    obtain ⟨A, hAcarrier, hAstart, hAend, hAarea⟩ :=
      exists_rectifiableOrientedArc_of_cut_with_area K' hαβ hx hne hbase
        hfrontier hinter hPt hQt hterminal hd hdir
    exact convexArcArea_eq_integral_of_cut_interior_nonempty K K' hαβ hx
      hAcarrier hAstart hAend hAarea rfl rfl hat htb hba hPt hQt hmiddle hleft hright
        hterminal hInt hd hdir
  · exact convexArcArea_eq_integral_of_cut_interior_empty K K' hat htb hba hne
      hPt hQt rfl rfl hleft hmiddle hright (Set.not_nonempty_iff_eq_empty.mp hInt)
      hd hdir

theorem convexArc_area (a b : ℝ) (hab : a < b) (hba : b < a + Real.pi) :
    (∀ K : ConvexBody Point, ∃ Γ : RectifiableOrientedArc,
      RealizesConvexArc K a b Γ ∧ convexArcArea K a b = jordanArcArea Γ ∧
      (Γ.val.startPoint = Γ.val.endPoint → Γ.val.carrier = {Γ.val.startPoint})) ∧
    (∀ K : ConvexBody Point, convexArcArea K a b =
      (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
        supportValue K t ∂surfaceAreaMeasure K) / 2) ∧
    IsQuadraticFunctional convexBodyCombination (fun K ↦ convexArcArea K a b) := by
  apply convexArc_area_of_realization_and_integral a b
    (exists_convexArc_realization a b hab hba)
  intro K
  by_cases heq : (edgeVertices K (a : Real.Angle)).1 =
      (edgeVertices K (b : Real.Angle)).2
  · exact convexArcArea_eq_integral_of_endpoints_eq K hab hba heq
  · exact convexArcArea_eq_integral_of_endpoints_ne K hab hba heq

end MovingSofa
