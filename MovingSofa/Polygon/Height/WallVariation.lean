import MovingSofa.Polygon.Nef.SignedVariation
import MovingSofa.Polygon.Nef.CapConstruction
import MovingSofa.Polygon.PerturbationBounds

noncomputable section
namespace MovingSofa

private theorem endpoint_wall_changes_disjoint (a : Real.Angle) (h ε : ℝ)
    (hε : 0 ≤ ε) (hε' : ε ≤ 1) (p : Point) :
    (p ∈ normalHalfPlane a (h + ε) false false ↔
      p ∈ normalHalfPlane a h false false) ∨
    (p ∈ normalHalfPlane a (h - 1 + ε) true false ↔
      p ∈ normalHalfPlane a (h - 1) true false) := by
  change (inner ℝ p (normalVector a) ≤ h + ε ↔ inner ℝ p (normalVector a) ≤ h) ∨
    (h - 1 + ε ≤ inner ℝ p (normalVector a) ↔ h - 1 ≤ inner ℝ p (normalVector a))
  by_cases hp : inner ℝ p (normalVector a) ≤ h
  · left
    constructor <;> intro _ <;> linarith
  · right
    constructor <;> intro _ <;> linarith

private theorem area_add_of_indicator_add_eq (A B C D : Set Point)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : MeasurableSet C) (hD : MeasurableSet D)
    (hAfin : MeasureTheory.volume A ≠ ⊤) (hBfin : MeasureTheory.volume B ≠ ⊤)
    (hCfin : MeasureTheory.volume C ≠ ⊤) (hDfin : MeasureTheory.volume D ≠ ⊤)
    (h : ∀ p, A.indicator (fun _ ↦ (1 : ℝ)) p + B.indicator (fun _ ↦ (1 : ℝ)) p =
      C.indicator (fun _ ↦ (1 : ℝ)) p + D.indicator (fun _ ↦ (1 : ℝ)) p) :
    ClassicalResults.area A + ClassicalResults.area B =
      ClassicalResults.area C + ClassicalResults.area D := by
  have hint (S : Set Point) (hm : MeasurableSet S) (hf : MeasureTheory.volume S ≠ ⊤) :
      MeasureTheory.Integrable (S.indicator (fun _ ↦ (1 : ℝ))) :=
    (MeasureTheory.integrableOn_const hf).integrable_indicator hm
  have heq := congrArg (fun f : Point → ℝ ↦ ∫ p, f p) (funext h)
  rw [MeasureTheory.integral_add (hint A hA hAfin) (hint B hB hBfin),
    MeasureTheory.integral_add (hint C hC hCfin) (hint D hD hDfin)] at heq
  have harea (S : Set Point) (hm : MeasurableSet S) :
      (∫ p, S.indicator (fun _ ↦ (1 : ℝ)) p) = ClassicalResults.area S :=
    MeasureTheory.integral_indicator_one hm
  simpa only [harea A hA, harea B hB, harea C hC, harea D hD] using heq
private def BooleanFunction.all (n : ℕ) : BooleanFunction n :=
  fun P ↦ decide (∀ i, P i = true)

private theorem BooleanFunction.all_monotone (n : ℕ) :
    IsMonotoneBooleanFunction (BooleanFunction.all n) := by
  intro P Q hPQ hP
  simp only [BooleanFunction.all, decide_eq_true_eq] at hP ⊢
  exact fun i ↦ hPQ i (hP i)

private theorem booleanSet_all {n : ℕ} (H : Fin n → Set Point) :
    booleanSet (BooleanFunction.all n) H = ⋂ i, H i := by
  classical
  ext p
  simp [booleanSet, BooleanFunction.all]

private theorem independentWallCap_eq_booleanSet {Θ : AngleSet}
    (h upper lower : PolygonHeightSpace Θ) {n : ℕ}
    (H : Fin n → PlanarHalfPlaneData) (hH : Set.range H = polygonCapWalls h)
    (F : PlanarHalfPlaneData → Set Point)
    (hupper : ∀ t ∈ angleDomain Θ,
      F ⟨(t : Real.Angle), polygonHeightValue h t, false, false⟩ =
        normalHalfPlane (t : Real.Angle) (polygonHeightValue upper t) false false)
    (hlower : ∀ t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
      F ⟨(t : Real.Angle), polygonHeightValue h t - 1, true, false⟩ =
        normalHalfPlane (t : Real.Angle) (polygonHeightValue lower t) true false) :
    independentWallCap upper lower =
      booleanSet (BooleanFunction.all n) (fun i ↦ F (H i)) := by
  rw [booleanSet_all]
  ext p
  have hrange : (∀ i, p ∈ F (H i)) ↔ ∀ W ∈ polygonCapWalls h, p ∈ F W := by
    rw [← hH]
    simp
  simp only [Set.mem_iInter]
  rw [hrange]
  simp only [independentWallCap, Set.mem_inter_iff, Set.mem_iInter]
  constructor
  · rintro ⟨hend, hint⟩ W hW
    rcases hW with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
    · rw [hupper t ht]
      rcases ht with ht | ht
      · exact hint t ht
      · exact (hend t ht).1
    · rw [hlower t ht]
      exact (hend t ht).2
  · intro hall
    constructor
    · intro t ht
      constructor
      · rw [← hupper t (Or.inr ht)]
        exact hall _ (Or.inl ⟨t, Or.inr ht, rfl⟩)
      · rw [← hlower t ht]
        exact hall _ (Or.inr ⟨t, ht, rfl⟩)
    · intro t ht
      rw [← hupper t (Or.inl ht)]
      exact hall _ (Or.inl ⟨t, Or.inl ht, rfl⟩)

private def BooleanFunction.niche (Θ : AngleSet) {n : ℕ}
    (endpoint : {t : ℝ // t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)} → Fin n)
    (left right : {t : ℝ // t ∈ Θ.directions} → Fin n) : BooleanFunction n := by
  classical
  exact fun P ↦ decide ((∀ t, P (endpoint t) = true) ∧
    ∃ t, P (left t) = true ∧ P (right t) = true)

private theorem BooleanFunction.niche_monotone (Θ : AngleSet) {n : ℕ}
    (endpoint : {t : ℝ // t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)} → Fin n)
    (left right : {t : ℝ // t ∈ Θ.directions} → Fin n) :
    IsMonotoneBooleanFunction (BooleanFunction.niche Θ endpoint left right) := by
  classical
  intro P Q hPQ hP
  simp only [BooleanFunction.niche, decide_eq_true_eq] at hP ⊢
  obtain ⟨he, t, hl, hr⟩ := hP
  exact ⟨fun s ↦ hPQ _ (he s), t, hPQ _ hl, hPQ _ hr⟩

private theorem independentWallNiche_eq_booleanSet {Θ : AngleSet}
    (lower : PolygonHeightSpace Θ) {n : ℕ} (H : Fin n → Set Point)
    (endpoint : {t : ℝ // t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)} → Fin n)
    (left right : {t : ℝ // t ∈ Θ.directions} → Fin n)
    (he : ∀ t, H (endpoint t) =
      normalHalfPlane (t.val : Real.Angle) (polygonHeightValue lower t.val) true false)
    (hl : ∀ t, H (left t) =
      normalHalfPlane (t.val : Real.Angle) (polygonHeightValue lower t.val) false true)
    (hr : ∀ t, H (right t) =
      normalHalfPlane ((t.val + Real.pi / 2 : ℝ) : Real.Angle)
        (polygonHeightValue lower (t.val + Real.pi / 2)) false true) :
    independentWallNiche lower =
      booleanSet (BooleanFunction.niche Θ endpoint left right) H := by
  classical
  ext p
  simp only [independentWallNiche, Set.mem_inter_iff, Set.mem_iInter,
    Set.mem_iUnion, booleanSet, Set.mem_ofPred_eq, BooleanFunction.niche,
    decide_eq_true_eq, he, hl, hr]
  constructor
  · rintro ⟨he, t, ht, hl, hr⟩
    exact ⟨fun s ↦ he s.val s.property, ⟨t, ht⟩, hl, hr⟩
  · rintro ⟨he, t, hl, hr⟩
    exact ⟨fun s hs ↦ he ⟨s, hs⟩, t.val, t.property, hl, hr⟩

private theorem exists_polygonNiche_wall_indices {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    {n : ℕ} (H : Fin n → PlanarHalfPlaneData)
    (hH : Set.range H = polygonNicheWalls h) :
    ∃ (endpoint : {t : ℝ // t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)} → Fin n)
      (left right : {t : ℝ // t ∈ Θ.directions} → Fin n),
      (∀ t, H (endpoint t) =
        ⟨(t.val : Real.Angle), polygonHeightValue h t.val - 1, true, false⟩) ∧
      (∀ t, H (left t) =
        ⟨(t.val : Real.Angle), polygonHeightValue h t.val - 1, false, true⟩) ∧
      (∀ t, H (right t) =
        ⟨((t.val + Real.pi / 2 : ℝ) : Real.Angle),
          polygonHeightValue h (t.val + Real.pi / 2) - 1, false, true⟩) := by
  classical
  have hpre (W : PlanarHalfPlaneData) (hW : W ∈ polygonNicheWalls h) :
      ∃ i, H i = W := by
    change W ∈ Set.range H
    rwa [hH]
  have he (t : {t : ℝ // t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)}) :
      ∃ i, H i = ⟨(t.val : Real.Angle), polygonHeightValue h t.val - 1, true, false⟩ :=
    hpre _ (Or.inr ⟨t.val, t.property, rfl⟩)
  have hl (t : {t : ℝ // t ∈ Θ.directions}) :
      ∃ i, H i = ⟨(t.val : Real.Angle), polygonHeightValue h t.val - 1, false, true⟩ :=
    hpre _ (Or.inl ⟨t.val, Or.inl t.property, rfl⟩)
  have hr (t : {t : ℝ // t ∈ Θ.directions}) :
      ∃ i, H i = ⟨((t.val + Real.pi / 2 : ℝ) : Real.Angle),
        polygonHeightValue h (t.val + Real.pi / 2) - 1, false, true⟩ :=
    hpre _ (Or.inl ⟨t.val + Real.pi / 2, Or.inr ⟨t.val, t.property, rfl⟩, rfl⟩)
  choose endpoint he using he
  choose left hl using hl
  choose right hr using hr
  exact ⟨endpoint, left, right, he, hl, hr⟩

private def PlanarHalfPlaneData.moveWall (W : PlanarHalfPlaneData) (δ : ℝ)
    (V : PlanarHalfPlaneData) : PlanarHalfPlaneData := by
  classical
  exact if V = W then {V with height := V.height + δ} else V

private theorem perturbNefHeight_eq_moveWall {n : ℕ} (E : BooleanFunction n)
    (H : Fin n → PlanarHalfPlaneData) (hH : Function.Injective H) (i : Fin n) (δ : ℝ) :
    perturbNefHeight E H i δ =
      booleanSet E (fun j ↦ ((H i).moveWall δ (H j)).carrier) := by
  classical
  unfold perturbNefHeight
  congr 1
  funext j
  simp only [PlanarHalfPlaneData.moveWall, hH.eq_iff]

/-- Angles in a polygon angle domain have distinct classes modulo a full turn. -/
theorem angleDomain_coe_injective (Θ : AngleSet) :
    Function.Injective (fun t : angleDomain Θ ↦ (t.val : Real.Angle)) := by
  intro s t hst
  apply Subtype.ext
  have hs := angleDomain_subset_Ioo Θ s.property
  have ht := angleDomain_subset_Ioo Θ t.property
  exact ((normalLine_eq_iff_of_mem_Ioo (c := 0) (d := 0) hs ht).mp
    (congrArg (fun a ↦ normalLine a 0) hst)).1

private theorem polygonHeightValue_update {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    (t : angleDomain Θ) (δ : ℝ) (s : ℝ) (hs : s ∈ angleDomain Θ) :
    polygonHeightValue (Function.update h t (h t + δ)) s =
      polygonHeightValue h s + if s = t.val then δ else 0 := by
  classical
  by_cases hst : s = t.val
  · subst s
    simp [polygonHeightValue, Function.update]
  · have hne : (⟨s, hs⟩ : angleDomain Θ) ≠ t := by
      intro heq
      exact hst (congrArg Subtype.val heq)
    simp [polygonHeightValue, Function.update, hs, hst, hne]

private theorem perturbNefHeight_cap_upper {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    {n : ℕ} (H : Fin n → PlanarHalfPlaneData)
    (hH : Set.range H = polygonCapWalls h) (hHinj : Function.Injective H)
    (i : Fin n) (t : angleDomain Θ)
    (hi : H i = ⟨(t.val : Real.Angle), h t, false, false⟩) (δ : ℝ) :
    perturbNefHeight (BooleanFunction.all n) H i δ =
      independentWallCap (Function.update h t (h t + δ)) (fun s ↦ h s - 1) := by
  classical
  rw [perturbNefHeight_eq_moveWall _ _ hHinj]
  symm
  apply independentWallCap_eq_booleanSet h _ _ H hH
    (fun W ↦ ((H i).moveWall δ W).carrier)
  · intro s hs
    have heq : (⟨(s : Real.Angle), polygonHeightValue h s, false, false⟩ :
        PlanarHalfPlaneData) = H i ↔ s = t.val := by
      rw [hi]
      constructor
      · intro heq
        have ha := congrArg PlanarHalfPlaneData.angle heq
        exact congrArg Subtype.val (angleDomain_coe_injective Θ
          (a₁ := ⟨s, hs⟩) (a₂ := t) ha)
      · intro hst
        subst s
        simp [polygonHeightValue]
    simp only [PlanarHalfPlaneData.moveWall, heq, polygonHeightValue_update h t δ s hs]
    split_ifs with hst
    · rfl
    · simp only [add_zero]
      rfl
  · intro s hs
    have hsD : s ∈ angleDomain Θ := Or.inr hs
    have hne : (⟨(s : Real.Angle), polygonHeightValue h s - 1, true, false⟩ :
        PlanarHalfPlaneData) ≠ H i := by
      rw [hi]
      intro heq
      have hb := congrArg PlanarHalfPlaneData.upper heq
      cases hb
    simp only [PlanarHalfPlaneData.moveWall, hne, ite_false]
    simp [PlanarHalfPlaneData.carrier, polygonHeightValue, hsD]

private theorem perturbNefHeight_cap_lower {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    {n : ℕ} (H : Fin n → PlanarHalfPlaneData)
    (hH : Set.range H = polygonCapWalls h) (hHinj : Function.Injective H)
    (i : Fin n) (t : angleDomain Θ)
    (hi : H i = ⟨(t.val : Real.Angle), h t - 1, true, false⟩) (δ : ℝ) :
    perturbNefHeight (BooleanFunction.all n) H i δ =
      independentWallCap h (Function.update (fun s ↦ h s - 1) t (h t - 1 + δ)) := by
  classical
  rw [perturbNefHeight_eq_moveWall _ _ hHinj]
  symm
  apply independentWallCap_eq_booleanSet h _ _ H hH
    (fun W ↦ ((H i).moveWall δ W).carrier)
  · intro s hs
    have hne : (⟨(s : Real.Angle), polygonHeightValue h s, false, false⟩ :
        PlanarHalfPlaneData) ≠ H i := by
      rw [hi]
      intro heq
      have hb := congrArg PlanarHalfPlaneData.upper heq
      cases hb
    simp only [PlanarHalfPlaneData.moveWall, hne, ite_false]
    rfl
  · intro s hs
    have hsD : s ∈ angleDomain Θ := Or.inr hs
    have heq : (⟨(s : Real.Angle), polygonHeightValue h s - 1, true, false⟩ :
        PlanarHalfPlaneData) = H i ↔ s = t.val := by
      rw [hi]
      constructor
      · intro heq
        have ha := congrArg PlanarHalfPlaneData.angle heq
        exact congrArg Subtype.val (angleDomain_coe_injective Θ
          (a₁ := ⟨s, hsD⟩) (a₂ := t) ha)
      · intro hst
        subst s
        simp [polygonHeightValue]
    simp only [PlanarHalfPlaneData.moveWall, heq,
      polygonHeightValue_update (fun s ↦ h s - 1) t δ s hsD]
    split_ifs <;> simp [PlanarHalfPlaneData.carrier, polygonHeightValue, hsD]

private theorem polygonCap_singleWall_uniform_bounds {Θ : AngleSet} (h : PolygonHeightSpace Θ) :
    ∃ R ε₀ : ℝ, 0 < R ∧ 0 < ε₀ ∧
      ∀ (n : ℕ) (H : Fin n → PlanarHalfPlaneData),
        Set.range H = polygonCapWalls h → Function.Injective H →
        ∀ (i : Fin n) (t : angleDomain Θ),
          (H i = ⟨(t.val : Real.Angle), h t, false, false⟩ ∨
            H i = ⟨(t.val : Real.Angle), h t - 1, true, false⟩) →
          ∀ δ : ℝ, |δ| ≤ ε₀ →
            perturbNefHeight (BooleanFunction.all n) H i δ ⊆ Metric.closedBall 0 R := by
  classical
  obtain ⟨R, ε₀, hR, hε₀, hb⟩ := polygonPerturbation_uniform_bounds Θ h
  refine ⟨R, ε₀, hR, hε₀, ?_⟩
  intro n H hH hHinj i t hi δ hδ
  have hupdate (f : PolygonHeightSpace Θ) :
      ∀ s, |Function.update f t (f t + δ) s - f s| ≤ ε₀ := by
    intro s
    by_cases hst : s = t
    · subst s
      simpa [Function.update] using hδ
    · simp [Function.update, hst, le_of_lt hε₀]
  rcases hi with hi | hi
  · rw [perturbNefHeight_cap_upper h H hH hHinj i t hi δ]
    exact (hb _ _ (hupdate h) (by intro s; simpa using le_of_lt hε₀)).1
  · rw [perturbNefHeight_cap_lower h H hH hHinj i t hi δ]
    exact (hb _ _ (by intro s; simpa using le_of_lt hε₀)
      (hupdate (fun s ↦ h s - 1))).1

private theorem perturbNefHeight_niche {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    {n : ℕ} (H : Fin n → PlanarHalfPlaneData)
    (hangle : Function.Injective (fun j ↦ (H j).angle))
    (endpoint : {t : ℝ // t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)} → Fin n)
    (left right : {t : ℝ // t ∈ Θ.directions} → Fin n)
    (he : ∀ t, H (endpoint t) =
      ⟨(t.val : Real.Angle), polygonHeightValue h t.val - 1, true, false⟩)
    (hl : ∀ t, H (left t) =
      ⟨(t.val : Real.Angle), polygonHeightValue h t.val - 1, false, true⟩)
    (hr : ∀ t, H (right t) =
      ⟨((t.val + Real.pi / 2 : ℝ) : Real.Angle),
        polygonHeightValue h (t.val + Real.pi / 2) - 1, false, true⟩)
    (i : Fin n) (t : angleDomain Θ) (hi : (H i).angle = (t.val : Real.Angle)) (δ : ℝ) :
    perturbNefHeight (BooleanFunction.niche Θ endpoint left right) H i δ =
      independentWallNiche (Function.update (fun s ↦ h s - 1) t (h t - 1 + δ)) := by
  classical
  have hwall (j : Fin n) (s : ℝ) (hs : s ∈ angleDomain Θ) (upper strict : Bool)
      (hj : H j = ⟨(s : Real.Angle), polygonHeightValue h s - 1, upper, strict⟩) :
      (if j = i then {H j with height := (H j).height + δ} else H j).carrier =
        normalHalfPlane (s : Real.Angle)
          (polygonHeightValue (Function.update (fun s ↦ h s - 1) t (h t - 1 + δ)) s)
          upper strict := by
    have hji : j = i ↔ s = t.val := by
      constructor
      · intro hji
        have ha : (s : Real.Angle) = (t.val : Real.Angle) := by
          rw [← hi, ← hji, hj]
        exact congrArg Subtype.val (angleDomain_coe_injective Θ
          (a₁ := ⟨s, hs⟩) (a₂ := t) ha)
      · intro hst
        apply hangle
        simp only [hj, hi, hst]
    simp only [hji, hj, polygonHeightValue_update (fun s ↦ h s - 1) t δ s hs]
    split_ifs <;> simp [PlanarHalfPlaneData.carrier, polygonHeightValue, hs]
  unfold perturbNefHeight
  symm
  apply independentWallNiche_eq_booleanSet _ _ endpoint left right
  · intro s
    exact hwall _ s.val (Or.inr s.property) true false (he s)
  · intro s
    exact hwall _ s.val (Or.inl (Or.inl s.property)) false true (hl s)
  · intro s
    exact hwall _ (s.val + Real.pi / 2)
      (Or.inl (Or.inr ⟨s.val, s.property, rfl⟩)) false true (hr s)

private theorem exists_angle_of_mem_polygonNicheWalls {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    (W : PlanarHalfPlaneData) (hW : W ∈ polygonNicheWalls h) :
    ∃ s : angleDomain Θ, W.angle = (s.val : Real.Angle) ∧ W.height = h s - 1 := by
  rcases hW with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
  · refine ⟨⟨s, Or.inl hs⟩, rfl, ?_⟩
    simp [polygonHeightValue, show s ∈ angleDomain Θ from Or.inl hs]
  · refine ⟨⟨s, Or.inr hs⟩, rfl, ?_⟩
    simp [polygonHeightValue, show s ∈ angleDomain Θ from Or.inr hs]

private theorem polygonNicheWalls_angle_injective {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    {n : ℕ} (H : Fin n → PlanarHalfPlaneData)
    (hH : Set.range H = polygonNicheWalls h)
    (hLines : Function.Injective (fun j ↦ (H j).boundaryLine)) :
    Function.Injective (fun j ↦ (H j).angle) := by
  intro i j hij
  obtain ⟨s, hs, hsheight⟩ := exists_angle_of_mem_polygonNicheWalls h
    (H i) (hH ▸ Set.mem_range_self i)
  obtain ⟨t, ht, htheight⟩ := exists_angle_of_mem_polygonNicheWalls h
    (H j) (hH ▸ Set.mem_range_self j)
  have hst : s = t := angleDomain_coe_injective Θ (hs.symm.trans (hij.trans ht))
  apply hLines
  simp only [PlanarHalfPlaneData.boundaryLine, hij, hsheight, htheight, hst]

private theorem exists_polygonNiche_perturbation_formula {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    {n : ℕ} (H : Fin n → PlanarHalfPlaneData)
    (hH : Set.range H = polygonNicheWalls h)
    (hLines : Function.Injective (fun j ↦ (H j).boundaryLine)) :
    ∃ E : BooleanFunction n, IsMonotoneBooleanFunction E ∧
      ∀ i, ∃ t : angleDomain Θ, (H i).angle = (t.val : Real.Angle) ∧
        ∀ δ : ℝ, perturbNefHeight E H i δ =
          independentWallNiche (Function.update (fun s ↦ h s - 1) t (h t - 1 + δ)) := by
  obtain ⟨endpoint, left, right, he, hl, hr⟩ := exists_polygonNiche_wall_indices h H hH
  refine ⟨BooleanFunction.niche Θ endpoint left right,
    BooleanFunction.niche_monotone Θ endpoint left right, ?_⟩
  intro i
  obtain ⟨t, ht, _⟩ := exists_angle_of_mem_polygonNicheWalls h
    (H i) (hH ▸ Set.mem_range_self i)
  refine ⟨t, ht, fun δ ↦ ?_⟩
  exact perturbNefHeight_niche h H (polygonNicheWalls_angle_injective h H hH hLines)
    endpoint left right he hl hr i t ht δ

/-- The niche with every lower wall shifted by one is the height-defined niche. -/
theorem independentWallNiche_sub_one {Θ : AngleSet} (h : PolygonHeightSpace Θ) :
    independentWallNiche (fun s ↦ h s - 1) = polygonHeightNiche h := by
  have hv (s : ℝ) (hs : s ∈ angleDomain Θ) :
      polygonHeightValue (fun s ↦ h s - 1) s = polygonHeightValue h s - 1 := by
    simp [polygonHeightValue, hs]
  unfold independentWallNiche polygonHeightNiche polygonHeightFan
  congr 1
  · apply Set.iInter_congr
    intro s
    apply Set.iInter_congr
    intro hs
    rw [hv s (Or.inr hs)]
  · apply Set.iUnion_congr
    intro s
    apply Set.iUnion_congr
    intro hs
    rw [hv s (Or.inl (Or.inl hs)),
      hv (s + Real.pi / 2) (Or.inl (Or.inr ⟨s, hs, rfl⟩))]

private theorem exists_polygonNiche_stable_presentation {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    {n : ℕ} (H : Fin n → PlanarHalfPlaneData)
    (hH : Set.range H = polygonNicheWalls h)
    (hLines : Function.Injective (fun j ↦ (H j).boundaryLine)) :
    ∃ (E : BooleanFunction n) (R ε₀ : ℝ),
      IsMonotoneBooleanFunction E ∧ 0 < R ∧ 0 < ε₀ ∧
      polygonHeightNiche h = booleanSet E (fun j ↦ (H j).carrier) ∧
      (∀ i, ∃ t : angleDomain Θ, (H i).angle = (t.val : Real.Angle) ∧
        ∀ δ : ℝ, perturbNefHeight E H i δ =
          independentWallNiche (Function.update (fun s ↦ h s - 1) t (h t - 1 + δ))) ∧
      ∀ i δ, |δ| ≤ ε₀ → perturbNefHeight E H i δ ⊆ Metric.closedBall 0 R := by
  classical
  obtain ⟨E, hE, htransport⟩ := exists_polygonNiche_perturbation_formula h H hH hLines
  obtain ⟨R, ε₀, hR, hε₀, hb⟩ := polygonPerturbation_uniform_bounds Θ h
  refine ⟨E, R, ε₀, hE, hR, hε₀, ?_, htransport, ?_⟩
  · have hW : (⟨(Θ.angle : Real.Angle), polygonHeightValue h Θ.angle - 1,
        true, false⟩ : PlanarHalfPlaneData) ∈ Set.range H := by
      rw [hH]
      exact Or.inr ⟨Θ.angle, by simp, rfl⟩
    obtain ⟨i, _⟩ := hW
    obtain ⟨t, _, ht⟩ := htransport i
    have hz := ht 0
    simpa [perturbNefHeight, independentWallNiche_sub_one] using hz.symm
  · intro i δ hδ
    obtain ⟨t, _, ht⟩ := htransport i
    rw [ht δ]
    apply (hb h _ (by intro s; simpa using le_of_lt hε₀) ?_).2
    intro s
    by_cases hst : s = t
    · subst s
      simpa [Function.update] using hδ
    · simp [Function.update, hst, le_of_lt hε₀]

end MovingSofa

namespace MovingSofa

/-- Quadratic area variation for any wall in a polygon-height niche presentation. -/
theorem polygonNiche_wall_area_variation {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    {n : ℕ} (H : Fin n → PlanarHalfPlaneData)
    (hH : Set.range H = polygonNicheWalls h)
    (hLines : Function.Injective (fun j ↦ (H j).boundaryLine)) (i : Fin n) :
    ∃ (t : angleDomain Θ) (C η : ℝ), (H i).angle = (t.val : Real.Angle) ∧
      0 ≤ C ∧ 0 < η ∧ ∀ δ : ℝ, |δ| ≤ η →
        |ClassicalResults.area
            (independentWallNiche (Function.update (fun s ↦ h s - 1) t (h t - 1 + δ))) -
          ClassicalResults.area (polygonHeightNiche h) -
          (if (H i).upper then -1 else 1) *
            (MeasureTheory.Measure.hausdorffMeasure 1
              (frontier (polygonHeightNiche h) ∩ (H i).boundaryLine)).toReal * δ| ≤
          C * δ ^ 2 := by
  classical
  obtain ⟨E, R, ε₀, hE, hR, hε₀, hbase, htransport, hbound⟩ :=
    exists_polygonNiche_stable_presentation h H hH hLines
  obtain ⟨t, ht, hmove⟩ := htransport i
  have hz : perturbNefHeight E H i 0 = polygonHeightNiche h := by
    simpa [perturbNefHeight] using hbase.symm
  obtain ⟨C, η, hC, hη, _, hvar⟩ := simpleNefPolygon_area_variation_signed
    E H i hE hLines R ε₀ hR hε₀ (hbound i)
  refine ⟨t, C, η, ht, hC, hη, ?_⟩
  intro δ hδ
  have hv := hvar δ hδ
  rw [hz, hmove δ] at hv
  exact hv

end MovingSofa

namespace MovingSofa

/-- The cap with every lower endpoint wall shifted by one is the height-defined cap. -/
theorem independentWallCap_sub_one {Θ : AngleSet} (h : PolygonHeightSpace Θ) :
    independentWallCap h (fun s ↦ h s - 1) = polygonHeightCap h := by
  unfold independentWallCap polygonHeightCap polygonHeightParallelogram
  congr 1
  apply Set.iInter_congr
  intro s
  apply Set.iInter_congr
  intro hs
  have hsD : s ∈ angleDomain Θ := Or.inr hs
  simp [polygonHeightValue, hsD]

/-- Quadratic area variation for one upper wall of a polygon-height cap. -/
theorem polygonCap_upper_wall_area_variation {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    {n : ℕ} (H : Fin n → PlanarHalfPlaneData)
    (hH : Set.range H = polygonCapWalls h)
    (hLines : Function.Injective (fun j ↦ (H j).boundaryLine))
    (i : Fin n) (t : angleDomain Θ)
    (hi : H i = ⟨(t.val : Real.Angle), h t, false, false⟩) :
    ∃ C η : ℝ, 0 ≤ C ∧ 0 < η ∧ ∀ δ : ℝ, |δ| ≤ η →
      |ClassicalResults.area
          (independentWallCap (Function.update h t (h t + δ)) (fun s ↦ h s - 1)) -
        ClassicalResults.area (polygonHeightCap h) -
        (MeasureTheory.Measure.hausdorffMeasure 1
          (frontier (polygonHeightCap h) ∩ (H i).boundaryLine)).toReal * δ| ≤
        C * δ ^ 2 := by
  classical
  have hHinj : Function.Injective H := by
    intro j k hjk
    exact hLines (congrArg PlanarHalfPlaneData.boundaryLine hjk)
  obtain ⟨R, ε₀, hR, hε₀, hbound⟩ := polygonCap_singleWall_uniform_bounds h
  have hmove := perturbNefHeight_cap_upper h H hH hHinj i t hi
  have hz : perturbNefHeight (BooleanFunction.all n) H i 0 = polygonHeightCap h := by
    rw [hmove 0]
    have hu : Function.update h t (h t + 0) = h := by
      funext s
      simp [Function.update]
      rintro rfl
      rfl
    rw [hu, independentWallCap_sub_one]
  obtain ⟨C, η, hC, hη, _, hvar⟩ := simpleNefPolygon_area_variation
    (BooleanFunction.all n) H i (BooleanFunction.all_monotone n) hLines
    (by rw [hi]) R ε₀ hR hε₀ (hbound n H hH hHinj i t (Or.inl hi))
  refine ⟨C, η, hC, hη, ?_⟩
  intro δ hδ
  have hv := hvar δ hδ
  rw [hz, hmove δ] at hv
  exact hv

end MovingSofa

namespace MovingSofa

/-- Quadratic area variation for one lower endpoint wall of a polygon-height cap. -/
theorem polygonCap_lower_wall_area_variation {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    {n : ℕ} (H : Fin n → PlanarHalfPlaneData)
    (hH : Set.range H = polygonCapWalls h)
    (hLines : Function.Injective (fun j ↦ (H j).boundaryLine))
    (i : Fin n) (t : angleDomain Θ)
    (hi : H i = ⟨(t.val : Real.Angle), h t - 1, true, false⟩) :
    ∃ C η : ℝ, 0 ≤ C ∧ 0 < η ∧ ∀ δ : ℝ, |δ| ≤ η →
      |ClassicalResults.area
          (independentWallCap h (Function.update (fun s ↦ h s - 1) t (h t - 1 + δ))) -
        ClassicalResults.area (polygonHeightCap h) +
        (MeasureTheory.Measure.hausdorffMeasure 1
          (frontier (polygonHeightCap h) ∩ (H i).boundaryLine)).toReal * δ| ≤
        C * δ ^ 2 := by
  classical
  have hHinj : Function.Injective H := by
    intro j k hjk
    exact hLines (congrArg PlanarHalfPlaneData.boundaryLine hjk)
  obtain ⟨R, ε₀, hR, hε₀, hbound⟩ := polygonCap_singleWall_uniform_bounds h
  have hmove := perturbNefHeight_cap_lower h H hH hHinj i t hi
  have hz : perturbNefHeight (BooleanFunction.all n) H i 0 = polygonHeightCap h := by
    simpa [independentWallCap_sub_one] using hmove 0
  obtain ⟨C, η, hC, hη, _, hvar⟩ := simpleNefPolygon_area_variation_lower
    (BooleanFunction.all n) H i (BooleanFunction.all_monotone n) hLines
    (by rw [hi]) R ε₀ hR hε₀ (hbound n H hH hHinj i t (Or.inr hi))
  refine ⟨C, η, hC, hη, ?_⟩
  intro δ hδ
  have hv := hvar δ hδ
  rw [hz, hmove δ] at hv
  exact hv

end MovingSofa

namespace MovingSofa

private theorem mem_independentWallCap_congr {Θ : AngleSet}
    (upper upper' lower lower' : PolygonHeightSpace Θ) (p : Point)
    (hu : ∀ s : angleDomain Θ,
      (inner ℝ p (normalVector (s.val : Real.Angle)) ≤ upper s ↔
        inner ℝ p (normalVector (s.val : Real.Angle)) ≤ upper' s))
    (hl : ∀ s : angleDomain Θ,
      (lower s ≤ inner ℝ p (normalVector (s.val : Real.Angle)) ↔
        lower' s ≤ inner ℝ p (normalVector (s.val : Real.Angle)))) :
    p ∈ independentWallCap upper lower ↔ p ∈ independentWallCap upper' lower' := by
  have hu' (s : ℝ) (hs : s ∈ angleDomain Θ) :
      p ∈ normalHalfPlane (s : Real.Angle) (polygonHeightValue upper s) false false ↔
        p ∈ normalHalfPlane (s : Real.Angle) (polygonHeightValue upper' s) false false := by
    simpa [normalHalfPlane, polygonHeightValue, hs] using hu ⟨s, hs⟩
  have hl' (s : ℝ) (hs : s ∈ angleDomain Θ) :
      p ∈ normalHalfPlane (s : Real.Angle) (polygonHeightValue lower s) true false ↔
        p ∈ normalHalfPlane (s : Real.Angle) (polygonHeightValue lower' s) true false := by
    simpa [normalHalfPlane, polygonHeightValue, hs] using hl ⟨s, hs⟩
  simp only [independentWallCap, Set.mem_inter_iff, Set.mem_iInter]
  constructor
  · rintro ⟨he, hi⟩
    exact ⟨fun s hs ↦ ⟨(hu' s (Or.inr hs)).mp (he s hs).1,
      (hl' s (Or.inr hs)).mp (he s hs).2⟩,
      fun s hs ↦ (hu' s (Or.inl hs)).mp (hi s hs)⟩
  · rintro ⟨he, hi⟩
    exact ⟨fun s hs ↦ ⟨(hu' s (Or.inr hs)).mpr (he s hs).1,
      (hl' s (Or.inr hs)).mpr (he s hs).2⟩,
      fun s hs ↦ (hu' s (Or.inl hs)).mpr (hi s hs)⟩

private theorem independentWallCap_indicator_update_add {Θ : AngleSet}
    (h : PolygonHeightSpace Θ) (t : angleDomain Θ) (ε : ℝ)
    (hε : 0 ≤ ε) (hε' : ε ≤ 1) (p : Point) :
    (independentWallCap (Function.update h t (h t + ε))
        (Function.update (fun s ↦ h s - 1) t (h t - 1 + ε))).indicator
        (fun _ ↦ (1 : ℝ)) p +
      (independentWallCap h (fun s ↦ h s - 1)).indicator (fun _ ↦ (1 : ℝ)) p =
      (independentWallCap (Function.update h t (h t + ε))
        (fun s ↦ h s - 1)).indicator (fun _ ↦ (1 : ℝ)) p +
      (independentWallCap h
        (Function.update (fun s ↦ h s - 1) t (h t - 1 + ε))).indicator
        (fun _ ↦ (1 : ℝ)) p := by
  classical
  have hsplit := endpoint_wall_changes_disjoint (t.val : Real.Angle) (h t) ε hε hε' p
  have hI (A B : Set Point) (hab : p ∈ A ↔ p ∈ B) :
      A.indicator (fun _ ↦ (1 : ℝ)) p = B.indicator (fun _ ↦ (1 : ℝ)) p := by
    by_cases ha : p ∈ A
    · rw [Set.indicator_of_mem ha, Set.indicator_of_mem (hab.mp ha)]
    · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem (fun hb ↦ ha (hab.mpr hb))]
  change (_ ↔ _) ∨ (_ ↔ _) at hsplit
  rcases hsplit with hu | hl
  · have hu' (s : angleDomain Θ) :
        inner ℝ p (normalVector (s.val : Real.Angle)) ≤ Function.update h t (h t + ε) s ↔
          inner ℝ p (normalVector (s.val : Real.Angle)) ≤ h s := by
      by_cases hst : s = t
      · subst s
        simpa [Function.update, normalHalfPlane] using hu
      · simp [Function.update, hst]
    have heq (lower : PolygonHeightSpace Θ) :=
      mem_independentWallCap_congr (Function.update h t (h t + ε)) h lower lower p
        hu' (fun _ ↦ Iff.rfl)
    exact (congrArg₂ (fun a b : ℝ ↦ a + b)
      (hI _ _ (heq (Function.update (fun s ↦ h s - 1) t (h t - 1 + ε)))) rfl).trans
      ((add_comm _ _).trans (congrArg₂ (fun a b : ℝ ↦ a + b)
        (hI _ _ (heq (fun s ↦ h s - 1))).symm rfl))
  · have hl' (s : angleDomain Θ) :
        Function.update (fun s ↦ h s - 1) t (h t - 1 + ε) s ≤
            inner ℝ p (normalVector (s.val : Real.Angle)) ↔
          h s - 1 ≤ inner ℝ p (normalVector (s.val : Real.Angle)) := by
      by_cases hst : s = t
      · subst s
        simpa [Function.update, normalHalfPlane] using hl
      · simp [Function.update, hst]
    have heq (upper : PolygonHeightSpace Θ) :=
      mem_independentWallCap_congr upper upper
        (Function.update (fun s ↦ h s - 1) t (h t - 1 + ε)) (fun s ↦ h s - 1) p
        (fun _ ↦ Iff.rfl) hl'
    exact congrArg₂ (fun a b : ℝ ↦ a + b)
      (hI _ _ (heq (Function.update h t (h t + ε)))) (hI _ _ (heq h)).symm

end MovingSofa

namespace MovingSofa

private theorem isClosed_independentWallCap {Θ : AngleSet} (upper lower : PolygonHeightSpace Θ) :
    IsClosed (independentWallCap upper lower) := by
  have hu (a : Real.Angle) (c : ℝ) : IsClosed (normalHalfPlane a c false false) :=
    isClosed_le (by fun_prop) continuous_const
  have hl (a : Real.Angle) (c : ℝ) : IsClosed (normalHalfPlane a c true false) :=
    isClosed_le continuous_const (by fun_prop)
  unfold independentWallCap
  exact (isClosed_iInter fun s ↦ isClosed_iInter fun _ ↦ (hu _ _).inter (hl _ _)).inter
    (isClosed_iInter fun s ↦ isClosed_iInter fun _ ↦ hu _ _)

/-- Simultaneous endpoint-wall variation is the sum of the two independent variations. -/
theorem independentWallCap_area_update_add {Θ : AngleSet}
    (h : PolygonHeightSpace Θ) (t : angleDomain Θ) (ε R : ℝ)
    (hε : 0 ≤ ε) (hε' : ε ≤ 1)
    (hbound : ∀ (upper lower : PolygonHeightSpace Θ),
      (upper = h ∨ upper = Function.update h t (h t + ε)) →
      (lower = (fun s ↦ h s - 1) ∨
        lower = Function.update (fun s ↦ h s - 1) t (h t - 1 + ε)) →
      independentWallCap upper lower ⊆ Metric.closedBall 0 R) :
    ClassicalResults.area (independentWallCap (Function.update h t (h t + ε))
        (Function.update (fun s ↦ h s - 1) t (h t - 1 + ε))) +
      ClassicalResults.area (independentWallCap h (fun s ↦ h s - 1)) =
      ClassicalResults.area (independentWallCap (Function.update h t (h t + ε))
        (fun s ↦ h s - 1)) +
      ClassicalResults.area (independentWallCap h
        (Function.update (fun s ↦ h s - 1) t (h t - 1 + ε))) := by
  have hf (upper lower : PolygonHeightSpace Θ)
      (hu : upper = h ∨ upper = Function.update h t (h t + ε))
      (hl : lower = (fun s ↦ h s - 1) ∨
        lower = Function.update (fun s ↦ h s - 1) t (h t - 1 + ε)) :
      MeasureTheory.volume (independentWallCap upper lower) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (MeasureTheory.measure_mono (hbound upper lower hu hl))
      MeasureTheory.measure_closedBall_lt_top)
  apply area_add_of_indicator_add_eq
  · exact (isClosed_independentWallCap _ _).measurableSet
  · exact (isClosed_independentWallCap _ _).measurableSet
  · exact (isClosed_independentWallCap _ _).measurableSet
  · exact (isClosed_independentWallCap _ _).measurableSet
  · exact hf _ _ (Or.inr rfl) (Or.inr rfl)
  · exact hf _ _ (Or.inl rfl) (Or.inl rfl)
  · exact hf _ _ (Or.inr rfl) (Or.inl rfl)
  · exact hf _ _ (Or.inl rfl) (Or.inr rfl)
  · exact independentWallCap_indicator_update_add h t ε hε hε'

end MovingSofa
