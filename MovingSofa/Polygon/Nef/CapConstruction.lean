import MovingSofa.Cap.AngleDomain
import MovingSofa.Geometry.NormalLines
import Mathlib.Data.Fintype.EquivFin
import MovingSofa.Polygon.Nef.Basic
import MovingSofa.Polygon.Height.Space

noncomputable section

namespace MovingSofa

def polygonCapWalls {Θ : AngleSet} (h : PolygonHeightSpace Θ) : Set PlanarHalfPlaneData :=
  (fun t : ℝ ↦ (⟨(t : Real.Angle), polygonHeightValue h t, false, false⟩ :
    PlanarHalfPlaneData)) '' angleDomain Θ ∪
  (fun t : ℝ ↦ (⟨(t : Real.Angle), polygonHeightValue h t - 1, true, false⟩ :
    PlanarHalfPlaneData)) '' {Θ.angle, Real.pi / 2}

def polygonNicheWalls {Θ : AngleSet} (h : PolygonHeightSpace Θ) : Set PlanarHalfPlaneData :=
  (fun t : ℝ ↦ (⟨(t : Real.Angle), polygonHeightValue h t - 1, false, true⟩ :
    PlanarHalfPlaneData)) ''
      ((Θ.directions : Set ℝ) ∪ ((fun t : ℝ ↦ t + Real.pi / 2) '' Θ.directions)) ∪
  (fun t : ℝ ↦ (⟨(t : Real.Angle), polygonHeightValue h t - 1, true, false⟩ :
    PlanarHalfPlaneData)) '' {Θ.angle, Real.pi / 2}

private theorem angleDomain_finite (Θ : AngleSet) : (angleDomain Θ).Finite := by
  unfold angleDomain
  exact (Θ.directions.finite_toSet.union
    (Θ.directions.finite_toSet.image (fun t : ℝ ↦ t + Real.pi / 2))).union
      (Set.finite_singleton (Real.pi / 2) |>.insert Θ.angle)

private theorem polygonInnerAngles_finite (Θ : AngleSet) :
    ((Θ.directions : Set ℝ) ∪
      ((fun t : ℝ ↦ t + Real.pi / 2) '' Θ.directions)).Finite :=
  Θ.directions.finite_toSet.union
    (Θ.directions.finite_toSet.image (fun t : ℝ ↦ t + Real.pi / 2))

private theorem polygonInnerAngles_subset_angleDomain (Θ : AngleSet) :
    (Θ.directions : Set ℝ) ∪
      ((fun t : ℝ ↦ t + Real.pi / 2) '' Θ.directions) ⊆ angleDomain Θ := by
  intro t ht
  exact Or.inl ht

private theorem polygonInnerAngle_ne_endpoint {Θ : AngleSet} {s t : ℝ}
    (hs : s ∈ (Θ.directions : Set ℝ) ∪
      ((fun r : ℝ ↦ r + Real.pi / 2) '' Θ.directions))
    (ht : t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) : s ≠ t := by
  rcases hs with hs | ⟨r, hr, rfl⟩
  · have hsI := Θ.interior s hs
    rcases ht with ht | ht
    · intro hst
      exact hsI.2.ne (hst.trans ht)
    · have ht' : t = Real.pi / 2 := by simpa using ht
      intro hst
      exact (ne_of_lt (hsI.2.trans_le Θ.angle_le)) (hst.trans ht')
  · have hrI := Θ.interior r hr
    rcases ht with ht | ht
    · intro hst
      have hgt : Θ.angle < r + Real.pi / 2 := by
        linarith [Θ.angle_le, hrI.1, Real.pi_pos]
      exact hgt.ne' (hst.trans ht)
    · have ht' : t = Real.pi / 2 := by simpa using ht
      intro hst
      have hgt : Real.pi / 2 < r + Real.pi / 2 := by linarith [hrI.1]
      exact hgt.ne' (hst.trans ht')

private theorem polygonCapWalls_finite {Θ : AngleSet} (h : PolygonHeightSpace Θ) :
    (polygonCapWalls h).Finite := by
  unfold polygonCapWalls
  exact ((angleDomain_finite Θ).image _).union
    ((Set.finite_singleton (Real.pi / 2) |>.insert Θ.angle).image _)

private theorem polygonNicheWalls_finite {Θ : AngleSet} (h : PolygonHeightSpace Θ) :
    (polygonNicheWalls h).Finite := by
  unfold polygonNicheWalls
  exact ((polygonInnerAngles_finite Θ).image _).union
    ((Set.finite_singleton (Real.pi / 2) |>.insert Θ.angle).image _)

private def polygonUpperWall {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    (t : ℝ) : PlanarHalfPlaneData :=
  ⟨(t : Real.Angle), polygonHeightValue h t, false, false⟩

private def polygonLowerWall {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    (t : ℝ) : PlanarHalfPlaneData :=
  ⟨(t : Real.Angle), polygonHeightValue h t - 1, true, false⟩

private def polygonInnerWall {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    (t : ℝ) : PlanarHalfPlaneData :=
  ⟨(t : Real.Angle), polygonHeightValue h t - 1, false, true⟩

private theorem polygonCapWalls_eq {Θ : AngleSet} (h : PolygonHeightSpace Θ) :
    polygonCapWalls h =
      polygonUpperWall h '' angleDomain Θ ∪
        polygonLowerWall h '' ({Θ.angle, Real.pi / 2} : Set ℝ) := by
  rfl

private theorem polygonNicheWalls_eq {Θ : AngleSet} (h : PolygonHeightSpace Θ) :
    polygonNicheWalls h =
      polygonInnerWall h ''
          ((Θ.directions : Set ℝ) ∪
            ((fun t : ℝ ↦ t + Real.pi / 2) '' Θ.directions)) ∪
        polygonLowerWall h '' ({Θ.angle, Real.pi / 2} : Set ℝ) := by
  rfl

private theorem boundaryLine_injOn_polygonCapWalls {Θ : AngleSet}
    (h : PolygonHeightSpace Θ) :
    Set.InjOn PlanarHalfPlaneData.boundaryLine (polygonCapWalls h) := by
  intro A hA B hB hline
  rw [polygonCapWalls_eq] at hA hB
  rcases hA with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩ <;>
    rcases hB with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
  · have hst := (normalLine_eq_iff_of_mem_Ioo
      (angleDomain_subset_Ioo Θ hs) (angleDomain_subset_Ioo Θ ht)).mp hline
    simp [hst.1]
  · have htD : t ∈ angleDomain Θ := Or.inr ht
    have hst := (normalLine_eq_iff_of_mem_Ioo
      (angleDomain_subset_Ioo Θ hs) (angleDomain_subset_Ioo Θ htD)).mp hline
    have hfalse := hst.2
    simp [polygonUpperWall, polygonLowerWall, hst.1] at hfalse
    exfalso
    linarith
  · have hsD : s ∈ angleDomain Θ := Or.inr hs
    have hst := (normalLine_eq_iff_of_mem_Ioo
      (angleDomain_subset_Ioo Θ hsD) (angleDomain_subset_Ioo Θ ht)).mp hline
    have hfalse := hst.2
    simp [polygonUpperWall, polygonLowerWall, hst.1] at hfalse
  · have hsD : s ∈ angleDomain Θ := Or.inr hs
    have htD : t ∈ angleDomain Θ := Or.inr ht
    have hst := (normalLine_eq_iff_of_mem_Ioo
      (angleDomain_subset_Ioo Θ hsD) (angleDomain_subset_Ioo Θ htD)).mp hline
    simp [hst.1]

private theorem boundaryLine_injOn_polygonNicheWalls {Θ : AngleSet}
    (h : PolygonHeightSpace Θ) :
    Set.InjOn PlanarHalfPlaneData.boundaryLine (polygonNicheWalls h) := by
  intro A hA B hB hline
  rw [polygonNicheWalls_eq] at hA hB
  rcases hA with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩ <;>
    rcases hB with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
  · have hsD := polygonInnerAngles_subset_angleDomain Θ hs
    have htD := polygonInnerAngles_subset_angleDomain Θ ht
    have hst := (normalLine_eq_iff_of_mem_Ioo
      (angleDomain_subset_Ioo Θ hsD) (angleDomain_subset_Ioo Θ htD)).mp hline
    simp [hst.1]
  · have hsD := polygonInnerAngles_subset_angleDomain Θ hs
    have htD : t ∈ angleDomain Θ := Or.inr ht
    have hst := (normalLine_eq_iff_of_mem_Ioo
      (angleDomain_subset_Ioo Θ hsD) (angleDomain_subset_Ioo Θ htD)).mp hline
    exact (polygonInnerAngle_ne_endpoint hs ht hst.1).elim
  · have hsD : s ∈ angleDomain Θ := Or.inr hs
    have htD := polygonInnerAngles_subset_angleDomain Θ ht
    have hst := (normalLine_eq_iff_of_mem_Ioo
      (angleDomain_subset_Ioo Θ hsD) (angleDomain_subset_Ioo Θ htD)).mp hline
    exact (polygonInnerAngle_ne_endpoint ht hs hst.1.symm).elim
  · have hsD : s ∈ angleDomain Θ := Or.inr hs
    have htD : t ∈ angleDomain Θ := Or.inr ht
    have hst := (normalLine_eq_iff_of_mem_Ioo
      (angleDomain_subset_Ioo Θ hsD) (angleDomain_subset_Ioo Θ htD)).mp hline
    simp [hst.1]

private def PositiveBooleanFormula.conjunctions {n : ℕ}
    (default : PositiveBooleanFormula n) :
    List (PositiveBooleanFormula n) → PositiveBooleanFormula n
  | [] => default
  | E :: Es => .conjunction E (conjunctions default Es)

private def PositiveBooleanFormula.disjunctions {n : ℕ}
    (default : PositiveBooleanFormula n) :
    List (PositiveBooleanFormula n) → PositiveBooleanFormula n
  | [] => default
  | E :: Es => .disjunction E (disjunctions default Es)

private theorem PositiveBooleanFormula.conjunctions_eval_eq_true {n : ℕ}
    (default : PositiveBooleanFormula n) (Es : List (PositiveBooleanFormula n))
    (P : Fin n → Bool) :
    (default.conjunctions Es).eval P = true ↔
      default.eval P = true ∧ ∀ E ∈ Es, E.eval P = true := by
  induction Es with
  | nil => simp [PositiveBooleanFormula.conjunctions]
  | cons E Es ih =>
      simp [PositiveBooleanFormula.conjunctions, PositiveBooleanFormula.eval, ih,
        and_left_comm]

private theorem PositiveBooleanFormula.disjunctions_eval_eq_true {n : ℕ}
    (default : PositiveBooleanFormula n) (Es : List (PositiveBooleanFormula n))
    (P : Fin n → Bool) :
    (default.disjunctions Es).eval P = true ↔
      default.eval P = true ∨ ∃ E ∈ Es, E.eval P = true := by
  induction Es with
  | nil => simp [PositiveBooleanFormula.disjunctions]
  | cons E Es ih =>
      simp [PositiveBooleanFormula.disjunctions, PositiveBooleanFormula.eval, ih,
        or_left_comm]

private theorem mem_polygonHeightCap_iff_walls {Θ : AngleSet}
    (h : PolygonHeightSpace Θ) (p : Point) :
    p ∈ polygonHeightCap h ↔
      ∀ W ∈ polygonCapWalls h, p ∈ W.carrier := by
  simp only [polygonHeightCap, polygonHeightParallelogram, polygonCapWalls,
    Set.mem_inter_iff, Set.mem_iInter, Set.mem_union, Set.mem_image]
  constructor
  · rintro ⟨hendpoint, hinner⟩ W
    rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · change p ∈ normalHalfPlane (t : Real.Angle) (polygonHeightValue h t) false false
      rcases ht with ht | ht
      · exact hinner t ht
      · exact (hendpoint t ht).1
    · change p ∈ normalHalfPlane (t : Real.Angle)
          (polygonHeightValue h t - 1) true false
      exact (hendpoint t ht).2
  · intro hall
    refine ⟨?_, ?_⟩
    · intro t ht
      constructor
      · exact hall (polygonUpperWall h t) (Or.inl ⟨t, Or.inr ht, rfl⟩)
      · exact hall (polygonLowerWall h t) (Or.inr ⟨t, ht, rfl⟩)
    · intro t ht
      exact hall (polygonUpperWall h t) (Or.inl ⟨t, Or.inl ht, rfl⟩)

private theorem mem_polygonHeightNiche_iff_walls {Θ : AngleSet}
    (h : PolygonHeightSpace Θ) (p : Point) :
    p ∈ polygonHeightNiche h ↔
      (∀ t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
        p ∈ (polygonLowerWall h t).carrier) ∧
      ∃ t ∈ Θ.directions,
        p ∈ (polygonInnerWall h t).carrier ∧
        p ∈ (polygonInnerWall h (t + Real.pi / 2)).carrier := by
  unfold polygonHeightNiche polygonHeightFan
  simp only [Set.mem_inter_iff, Set.mem_iInter]
  constructor
  · rintro ⟨hfan, hniche⟩
    refine ⟨?_, ?_⟩
    · intro t ht
      exact hfan t ht
    · obtain ⟨t, ht, hp⟩ := Set.mem_iUnion₂.mp hniche
      exact ⟨t, ht, hp⟩
  · rintro ⟨hfan, t, ht, hp⟩
    refine ⟨hfan, Set.mem_iUnion₂.mpr ⟨t, ht, ?_⟩⟩
    exact hp

private theorem exists_polygonHeightCap_simpleNef (Θ : AngleSet)
    (h : PolygonHeightSpace Θ) :
    ∃ (n : ℕ) (H : Fin n → PlanarHalfPlaneData),
      Set.range H = polygonCapWalls h ∧
        IsSimpleNefPolygonWith (polygonHeightCap h) H := by
  classical
  let S : Set PlanarHalfPlaneData := polygonCapWalls h
  have hSfinite : S.Finite := polygonCapWalls_finite h
  let _ : Fintype S := hSfinite.fintype
  let n := Fintype.card S
  let e : Fin n ≃ S := (Fintype.equivFin S).symm
  let H : Fin n → PlanarHalfPlaneData := fun i ↦ (e i).1
  have hrange : Set.range H = polygonCapWalls h := by
    ext W
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).2
    · intro hW
      obtain ⟨i, hi⟩ := e.surjective ⟨W, hW⟩
      exact ⟨i, congrArg Subtype.val hi⟩
  have hHinj : Function.Injective (fun i ↦ (H i).boundaryLine) := by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    exact boundaryLine_injOn_polygonCapWalls h (e i).2 (e j).2 hij
  have hupperω : polygonUpperWall h Θ.angle ∈ S := by
    exact Or.inl ⟨Θ.angle, by simp [angleDomain], rfl⟩
  let i₀ : Fin n := e.symm ⟨polygonUpperWall h Θ.angle, hupperω⟩
  let varList : List (PositiveBooleanFormula n) :=
    List.ofFn fun i : Fin n ↦ PositiveBooleanFormula.variable i
  let formula : PositiveBooleanFormula n :=
    (PositiveBooleanFormula.variable i₀).conjunctions varList
  refine ⟨n, H, hrange, hHinj, formula.eval,
    positiveBooleanFormula_monotone formula, ?_⟩
  ext p
  rw [mem_polygonHeightCap_iff_walls]
  change (∀ W ∈ polygonCapWalls h, p ∈ W.carrier) ↔
    formula.eval (fun i ↦ decide (p ∈ (H i).carrier)) = true
  have hformula (P : Fin n → Bool) :
      formula.eval P = true ↔ ∀ i, P i = true := by
    rw [show formula = (PositiveBooleanFormula.variable i₀).conjunctions varList by rfl,
      PositiveBooleanFormula.conjunctions_eval_eq_true]
    simp [varList, PositiveBooleanFormula.eval]
    aesop
  rw [hformula]
  constructor
  · intro hall i
    apply decide_eq_true
    exact hall (H i) (e i).2
  · intro hall W hW
    obtain ⟨i, hi⟩ := e.surjective ⟨W, hW⟩
    have hi' : H i = W := congrArg Subtype.val hi
    subst W
    exact of_decide_eq_true (hall i)

private theorem exists_polygonHeightNiche_simpleNef (Θ : AngleSet)
    (h : PolygonHeightSpace Θ) :
    ∃ (n : ℕ) (H : Fin n → PlanarHalfPlaneData),
      Set.range H = polygonNicheWalls h ∧
        IsSimpleNefPolygonWith (polygonHeightNiche h) H := by
  classical
  let S : Set PlanarHalfPlaneData := polygonNicheWalls h
  have hSfinite : S.Finite := polygonNicheWalls_finite h
  let _ : Fintype S := hSfinite.fintype
  let n := Fintype.card S
  let e : Fin n ≃ S := (Fintype.equivFin S).symm
  let H : Fin n → PlanarHalfPlaneData := fun i ↦ (e i).1
  have hrange : Set.range H = polygonNicheWalls h := by
    ext W
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).2
    · intro hW
      obtain ⟨i, hi⟩ := e.surjective ⟨W, hW⟩
      exact ⟨i, congrArg Subtype.val hi⟩
  have hHinj : Function.Injective (fun i ↦ (H i).boundaryLine) := by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    exact boundaryLine_injOn_polygonNicheWalls h (e i).2 (e j).2 hij
  have hlowerω : polygonLowerWall h Θ.angle ∈ S := by
    exact Or.inr ⟨Θ.angle, by simp, rfl⟩
  have hlowerT : polygonLowerWall h (Real.pi / 2) ∈ S := by
    exact Or.inr ⟨Real.pi / 2, by simp, rfl⟩
  have hinner (t : ℝ) (ht : t ∈ Θ.directions) :
      polygonInnerWall h t ∈ S := by
    exact Or.inl ⟨t, Or.inl ht, rfl⟩
  have hinnerShift (t : ℝ) (ht : t ∈ Θ.directions) :
      polygonInnerWall h (t + Real.pi / 2) ∈ S := by
    exact Or.inl ⟨t + Real.pi / 2, Or.inr ⟨t, ht, rfl⟩, rfl⟩
  let iω : Fin n := e.symm ⟨polygonLowerWall h Θ.angle, hlowerω⟩
  let iT : Fin n := e.symm ⟨polygonLowerWall h (Real.pi / 2), hlowerT⟩
  let innerIndex : Θ.directions → Fin n :=
    fun t ↦ e.symm ⟨polygonInnerWall h t, hinner t t.property⟩
  let shiftedIndex : Θ.directions → Fin n :=
    fun t ↦ e.symm ⟨polygonInnerWall h (t + Real.pi / 2), hinnerShift t t.property⟩
  let pairFormula : Θ.directions → PositiveBooleanFormula n :=
    fun t ↦ .conjunction (.variable (innerIndex t)) (.variable (shiftedIndex t))
  let t₀ : Θ.directions := ⟨Θ.nonempty.choose, Θ.nonempty.choose_spec⟩
  let pairList : List (PositiveBooleanFormula n) :=
    Θ.directions.attach.toList.map pairFormula
  let endpointFormula : PositiveBooleanFormula n :=
    .conjunction (.variable iω) (.variable iT)
  let interiorFormula : PositiveBooleanFormula n :=
    (pairFormula t₀).disjunctions pairList
  let formula : PositiveBooleanFormula n :=
    .conjunction endpointFormula interiorFormula
  have hHiω : H iω = polygonLowerWall h Θ.angle := by
    exact congrArg Subtype.val (e.apply_symm_apply
      ⟨polygonLowerWall h Θ.angle, hlowerω⟩)
  have hHiT : H iT = polygonLowerWall h (Real.pi / 2) := by
    exact congrArg Subtype.val (e.apply_symm_apply
      ⟨polygonLowerWall h (Real.pi / 2), hlowerT⟩)
  have hHinner (t : Θ.directions) :
      H (innerIndex t) = polygonInnerWall h t := by
    exact congrArg Subtype.val (e.apply_symm_apply
      ⟨polygonInnerWall h t, hinner t t.property⟩)
  have hHshift (t : Θ.directions) :
      H (shiftedIndex t) = polygonInnerWall h (t + Real.pi / 2) := by
    exact congrArg Subtype.val (e.apply_symm_apply
      ⟨polygonInnerWall h (t + Real.pi / 2), hinnerShift t t.property⟩)
  refine ⟨n, H, hrange, hHinj, formula.eval,
    positiveBooleanFormula_monotone formula, ?_⟩
  ext p
  rw [mem_polygonHeightNiche_iff_walls]
  change ((∀ t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
      p ∈ (polygonLowerWall h t).carrier) ∧
    ∃ t ∈ Θ.directions,
      p ∈ (polygonInnerWall h t).carrier ∧
      p ∈ (polygonInnerWall h (t + Real.pi / 2)).carrier) ↔
    formula.eval (fun i ↦ decide (p ∈ (H i).carrier)) = true
  have hpair (t : Θ.directions) (P : Fin n → Bool) :
      (pairFormula t).eval P = true ↔
        P (innerIndex t) = true ∧ P (shiftedIndex t) = true := by
    simp [pairFormula, PositiveBooleanFormula.eval]
  have hinterior (P : Fin n → Bool) :
      interiorFormula.eval P = true ↔
        ∃ t : Θ.directions,
          P (innerIndex t) = true ∧ P (shiftedIndex t) = true := by
    rw [show interiorFormula = (pairFormula t₀).disjunctions pairList by rfl,
      PositiveBooleanFormula.disjunctions_eval_eq_true]
    simp only [hpair]
    constructor
    · rintro (ht₀ | ⟨E, hE, hEval⟩)
      · exact ⟨t₀, ht₀⟩
      · rw [show pairList = Θ.directions.attach.toList.map pairFormula by rfl] at hE
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hE
        exact ⟨t, (hpair t P).mp hEval⟩
    · rintro ⟨t, hEval⟩
      right
      refine ⟨pairFormula t, ?_, (hpair t P).mpr hEval⟩
      rw [show pairList = Θ.directions.attach.toList.map pairFormula by rfl]
      exact List.mem_map.mpr ⟨t, by simp, rfl⟩
  have hformula (P : Fin n → Bool) :
      formula.eval P = true ↔
        (P iω = true ∧ P iT = true) ∧
          ∃ t : Θ.directions,
            P (innerIndex t) = true ∧ P (shiftedIndex t) = true := by
    rw [show formula = .conjunction endpointFormula interiorFormula by rfl]
    simp only [PositiveBooleanFormula.eval, Bool.and_eq_true, hinterior]
    simp [endpointFormula, PositiveBooleanFormula.eval]
  rw [hformula]
  constructor
  · rintro ⟨hendpoint, t, ht, htinner, htshift⟩
    let ts : Θ.directions := ⟨t, ht⟩
    refine ⟨⟨?_, ?_⟩, ts, ?_, ?_⟩
    · apply decide_eq_true
      rw [hHiω]
      exact hendpoint Θ.angle (by simp)
    · apply decide_eq_true
      rw [hHiT]
      exact hendpoint (Real.pi / 2) (by simp)
    · apply decide_eq_true
      rw [hHinner ts]
      exact htinner
    · apply decide_eq_true
      rw [hHshift ts]
      exact htshift
  · rintro ⟨⟨hω, hT⟩, t, htinner, htshift⟩
    refine ⟨?_, t, t.property, ?_, ?_⟩
    · intro s hs
      rcases hs with hs | hs
      · have hsval : s = Θ.angle := hs
        subst s
        rw [← hHiω]
        exact of_decide_eq_true hω
      · have hsval : s = Real.pi / 2 := by simpa using hs
        subst s
        rw [← hHiT]
        exact of_decide_eq_true hT
    · rw [← hHinner t]
      exact of_decide_eq_true htinner
    · rw [← hHshift t]
      exact of_decide_eq_true htshift

theorem polygonCap_niche_simpleNef (Θ : AngleSet) (h : PolygonHeightSpace Θ) :
    (∃ (n : ℕ) (H : Fin n → PlanarHalfPlaneData),
      Set.range H = polygonCapWalls h ∧ IsSimpleNefPolygonWith (polygonHeightCap h) H) ∧
    (∃ (n : ℕ) (H : Fin n → PlanarHalfPlaneData),
      Set.range H = polygonNicheWalls h ∧ IsSimpleNefPolygonWith (polygonHeightNiche h) H) := by
  exact ⟨exists_polygonHeightCap_simpleNef Θ h, exists_polygonHeightNiche_simpleNef Θ h⟩

end MovingSofa
