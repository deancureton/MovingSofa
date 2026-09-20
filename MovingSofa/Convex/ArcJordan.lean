import MovingSofa.Convex.ArcArea
import TauCeti.Analysis.Normed.Module.FilledHull

noncomputable section

namespace MovingSofa

open Set

/-- A rectifiable path traverses a segment with monotone surjective reparametrizations. -/
def IsSegmentTraversal (γ : RectifiablePathData) (P Q : Point) : Prop :=
  ∃ (φ : Set.Icc (0 : ℝ) 1 → Set.Icc γ.a γ.b)
    (τ : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1),
    Continuous φ ∧ Monotone φ ∧ Function.Surjective φ ∧
    Continuous τ ∧ Monotone τ ∧ Function.Surjective τ ∧
    ∀ s, γ.path.val (φ s) = (1 - (τ s : ℝ)) • P + (τ s : ℝ) • Q

/-- A rectifiable path traverses an oriented Jordan arc in reverse. -/
def IsReverseArcTraversal (γ : RectifiablePathData) {A : OrientedJordanArc}
    (p : ArcBVParametrization A) : Prop :=
  ∃ (φ : Set.Icc (0 : ℝ) 1 → Set.Icc γ.a γ.b)
    (ψ : Set.Icc (0 : ℝ) 1 → Set.Icc p.a p.b),
    Continuous φ ∧ Monotone φ ∧ Function.Surjective φ ∧
    Continuous ψ ∧ Monotone ψ ∧ Function.Surjective ψ ∧
    ∀ s, γ.path.val (φ s) = p.path.val
      ⟨p.a + p.b - (ψ s : ℝ), by
        constructor <;> linarith [(ψ s).property.1, (ψ s).property.2]⟩

/-- A path traversing an oriented segment has the segment's signed area. -/
theorem IsSegmentTraversal.curveAreaFunctional_eq {γ : RectifiablePathData} {P Q : Point}
    (h : IsSegmentTraversal γ P Q) : curveAreaFunctional γ.path = segmentArea P Q := by
  obtain ⟨φ, τ, hφc, hφm, hφs, hτc, hτm, hτs, heq⟩ := h
  obtain ⟨y, hy, hymono, -⟩ := curveArea_comp_monotone_or_antitone_surjective
    γ.ordered zero_le_one γ.path φ hφc hφs (Or.inl hφm)
  obtain ⟨y', hy', hy'mono, -⟩ := curveArea_comp_monotone_or_antitone_surjective
    zero_le_one zero_le_one (lineSegmentBVPath P Q) τ hτc hτs (Or.inl hτm)
  have hyy : y = y' := by
    refine Subtype.ext ?_
    rw [hy, hy']
    funext s
    rw [Function.comp_apply, Function.comp_apply, heq s, lineSegmentBVPath_apply]
  rw [← hymono hφm, hyy, hy'mono hτm, curveAreaFunctional_lineSegmentBVPath]

/-- A path traversing an oriented Jordan arc backwards has the opposite signed area. -/
theorem IsReverseArcTraversal.curveAreaFunctional_eq {γ : RectifiablePathData}
    {A : OrientedJordanArc} {p : ArcBVParametrization A} (h : IsReverseArcTraversal γ p) :
    curveAreaFunctional γ.path = -curveAreaFunctional p.path := by
  obtain ⟨φ, ψ, hφc, hφm, hφs, hψc, hψm, hψs, heq⟩ := h
  set ρ : Set.Icc (0 : ℝ) 1 → Set.Icc p.a p.b := fun s ↦
    ⟨p.a + p.b - (ψ s : ℝ), by
      constructor <;> linarith [(ψ s).property.1, (ψ s).property.2]⟩ with hρdef
  have hcomp : ∀ s, γ.path.val (φ s) = p.path.val (ρ s) := heq
  have hρc : Continuous ρ :=
    (continuous_const.sub (continuous_subtype_val.comp hψc)).subtype_mk _
  have hρa : Antitone ρ := fun s t hst ↦
    Subtype.coe_le_coe.mp (by
      simp only [hρdef]
      linarith [Subtype.coe_le_coe.mpr (hψm hst)])
  have hρs : Function.Surjective ρ := by
    intro u
    obtain ⟨s, hs⟩ := hψs ⟨p.a + p.b - (u : ℝ), by
      constructor <;> linarith [u.property.1, u.property.2]⟩
    refine ⟨s, Subtype.ext ?_⟩
    have hval : ((ψ s : ℝ)) = p.a + p.b - (u : ℝ) := congrArg Subtype.val hs
    simp only [hρdef, hval]
    ring
  obtain ⟨y, hy, hymono, -⟩ := curveArea_comp_monotone_or_antitone_surjective
    γ.ordered zero_le_one γ.path φ hφc hφs (Or.inl hφm)
  obtain ⟨y', hy', -, hy'anti⟩ := curveArea_comp_monotone_or_antitone_surjective
    p.ordered zero_le_one p.path ρ hρc hρs (Or.inr hρa)
  have hyy : y = y' := by
    refine Subtype.ext ?_
    rw [hy, hy']
    funext s
    exact hcomp s
  rw [← hymono hφm, hyy, hy'anti hρa]

private def reverseArcPath {A : OrientedJordanArc} (p : ArcBVParametrization A) :
    ContinuousBVPaths p.a p.b where
  val := p.path.val ∘ Set.Icc.reverse p.ordered
  property := by
    constructor
    · exact p.path.property.1.comp (Set.Icc.continuous_reverse p.ordered)
    · intro i
      exact BoundedVariationOn.comp_antitone_surjective_Icc p.ordered
        (p.path.property.2 i) (Set.Icc.antitone_reverse p.ordered)
        (Set.Icc.surjective_reverse p.ordered)

private lemma reverseArcPath_start {A : OrientedJordanArc}
    (p : ArcBVParametrization A) :
    (reverseArcPath p).val ⟨p.a, le_rfl, p.ordered⟩ = A.endPoint := by
  simpa [reverseArcPath, Set.Icc.reverse] using p.end_eq

private lemma isSegmentTraversal_lineSegmentBVPath (P Q : Point) :
    IsSegmentTraversal
      { a := 0, b := 1, ordered := by norm_num, path := lineSegmentBVPath P Q } P Q := by
  refine ⟨id, id, continuous_id, monotone_id, Function.surjective_id,
    continuous_id, monotone_id, Function.surjective_id, ?_⟩
  intro s
  simp [lineSegmentBVPath, Path.segment_apply, AffineMap.lineMap_apply_module']
  module

private theorem boundedVariation_concatUnitIntervals_coordinate_jordan
    (p q : ContinuousBVPaths 0 1)
    (hjoin : p.val ⟨1, by norm_num⟩ = q.val ⟨0, by norm_num⟩) (i : Fin 2) :
    BoundedVariationOn (fun t ↦ Function.concatUnitIntervals p.val q.val t i) Set.univ := by
  let z : Set.Icc (0 : ℝ) 2 := ⟨0, by norm_num⟩
  let o : Set.Icc (0 : ℝ) 2 := ⟨1, by norm_num⟩
  let w : Set.Icc (0 : ℝ) 2 := ⟨2, by norm_num⟩
  let f := fun t ↦ Function.concatUnitIntervals p.val q.val t i
  have hzo : z ≤ o := by change (0 : ℝ) ≤ 1; norm_num
  have how : o ≤ w := by change (1 : ℝ) ≤ 2; norm_num
  have hsplit := eVariationOn.Icc_add_Icc f hzo how (Set.mem_univ o)
  simp only [Set.univ_inter] at hsplit
  have hwhole : Set.Icc z w = Set.univ := by
    ext t
    exact iff_true_intro t.property
  rw [hwhole] at hsplit
  change eVariationOn f Set.univ ≠ ⊤
  rw [← hsplit]
  apply ENNReal.add_ne_top.mpr
  constructor
  · refine ne_top_of_le_ne_top (p.property.2 i) ?_
    calc
      eVariationOn f (Set.Icc z o) =
          eVariationOn (fun t : Set.Icc (0 : ℝ) 2 ↦
            p.val (Set.projIcc 0 1 (by norm_num) (t : ℝ)) i) (Set.Icc z o) := by
              apply eVariationOn.congr
              intro t ht
              have ht' : (t : ℝ) ≤ 1 := by exact ht.2
              simp [f, Function.concatUnitIntervals, ht']
      _ ≤ eVariationOn (fun t ↦ p.val t i) Set.univ := by
        simpa only [Function.comp_def] using
          (eVariationOn.comp_le_of_monotoneOn (fun t ↦ p.val t i)
            (t := Set.Icc z o)
            (fun t : Set.Icc (0 : ℝ) 2 ↦ Set.projIcc 0 1 (by norm_num) (t : ℝ))
            (fun _ _ _ _ hxy ↦ Set.monotone_projIcc (by norm_num) hxy)
            (Set.mapsTo_univ _ _))
  · refine ne_top_of_le_ne_top (q.property.2 i) ?_
    calc
      eVariationOn f (Set.Icc o w) =
          eVariationOn (fun t : Set.Icc (0 : ℝ) 2 ↦
            q.val (Set.projIcc 0 1 (by norm_num) ((t : ℝ) - 1)) i) (Set.Icc o w) := by
              apply eVariationOn.congr
              intro t ht
              have hleft : (1 : ℝ) ≤ t := by exact ht.1
              have ht' : ¬(t : ℝ) ≤ 1 ∨ (t : ℝ) = 1 := by
                rcases lt_or_eq_of_le hleft with h | h
                · exact Or.inl (not_le_of_gt h)
                · exact Or.inr h.symm
              rcases ht' with ht' | htEq
              · simp [f, Function.concatUnitIntervals, ht']
              · simpa [f, Function.concatUnitIntervals, htEq] using
                  congrArg (fun z ↦ z i) hjoin
      _ ≤ eVariationOn (fun t ↦ q.val t i) Set.univ := by
        simpa only [Function.comp_def] using
          (eVariationOn.comp_le_of_monotoneOn (fun t ↦ q.val t i)
            (t := Set.Icc o w)
            (fun t : Set.Icc (0 : ℝ) 2 ↦
              Set.projIcc 0 1 (by norm_num) ((t : ℝ) - 1))
            (fun _ _ _ _ hxy ↦ Set.monotone_projIcc (by norm_num)
              (sub_le_sub_right (show (_ : ℝ) ≤ _ from hxy) 1))
            (Set.mapsTo_univ _ _))

private def concatUnitPaths_jordan (p q : ContinuousBVPaths 0 1)
    (hjoin : p.val ⟨1, by norm_num⟩ = q.val ⟨0, by norm_num⟩) :
    ContinuousBVPaths 0 2 :=
  ⟨Function.concatUnitIntervals p.val q.val,
    Function.continuous_concatUnitIntervals p.property.1 q.property.1 hjoin,
    boundedVariation_concatUnitIntervals_coordinate_jordan p q hjoin⟩

private lemma concatUnitPaths_jordan_end (p q : ContinuousBVPaths 0 1)
    (hjoin : p.val ⟨1, by norm_num⟩ = q.val ⟨0, by norm_num⟩) :
    (concatUnitPaths_jordan p q hjoin).val ⟨2, by norm_num⟩ =
      q.val ⟨1, by norm_num⟩ := by
  change Function.concatUnitIntervals p.val q.val ⟨2, by norm_num⟩ = _
  unfold Function.concatUnitIntervals
  simp only
  rw [ite_eq_right (by norm_num : ¬(2 : ℝ) ≤ 1)]
  apply congrArg q.val
  apply Subtype.ext
  norm_num

private def unitParam_jordan (a b : ℝ) (hab : a ≤ b) :
    Set.Icc (0 : ℝ) 1 → Set.Icc a b :=
  Set.Icc.convexComb ⟨a, le_rfl, hab⟩ ⟨b, hab, le_rfl⟩

private lemma continuous_unitParam_jordan (a b : ℝ) (hab : a ≤ b) :
    Continuous (unitParam_jordan a b hab) :=
  Set.Icc.continuous_convexComb _ _

private lemma monotone_unitParam_jordan (a b : ℝ) (hab : a ≤ b) :
    Monotone (unitParam_jordan a b hab) := by
  intro s t hst
  apply Subtype.coe_le_coe.mp
  simp only [unitParam_jordan, Set.Icc.coe_convexComb]
  nlinarith [show (s : ℝ) ≤ t from hst]

private lemma surjective_unitParam_jordan (a b : ℝ) (hab : a ≤ b) :
    Function.Surjective (unitParam_jordan a b hab) :=
  surjective_convexComb_endpoints a b hab

private theorem exists_reverseArcUnitPath {A : OrientedJordanArc}
    (p : ArcBVParametrization A) :
    ∃ q : ContinuousBVPaths 0 1,
      q.val = (reverseArcPath p).val ∘ unitParam_jordan p.a p.b p.ordered ∧
      IsReverseArcTraversal
        { a := 0, b := 1, ordered := by norm_num, path := q } p := by
  obtain ⟨q, hq⟩ := continuousBVPaths_comp_monotone_surjective p.ordered
    (reverseArcPath p) (unitParam_jordan p.a p.b p.ordered)
    (continuous_unitParam_jordan _ _ _) (monotone_unitParam_jordan _ _ _)
    (surjective_unitParam_jordan _ _ _)
  refine ⟨q, hq, ?_⟩
  let φ : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1 := id
  let ψ := unitParam_jordan p.a p.b p.ordered
  refine ⟨φ, ψ, continuous_id, monotone_id, Function.surjective_id,
    continuous_unitParam_jordan _ _ _, monotone_unitParam_jordan _ _ _,
    surjective_unitParam_jordan _ _ _, ?_⟩
  intro s
  rw [hq]
  change p.path.val (Set.Icc.reverse p.ordered (ψ s)) = p.path.val _
  simp only [ψ, unitParam_jordan, Set.Icc.reverse, Set.Icc.coe_convexComb]

private def doubleParam_jordan : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 2 :=
  fun t ↦ ⟨2 * (t : ℝ), by constructor <;> nlinarith [t.property.1, t.property.2]⟩

private lemma continuous_doubleParam_jordan : Continuous doubleParam_jordan :=
  Continuous.subtype_mk (continuous_const.mul continuous_subtype_val) _

private lemma monotone_doubleParam_jordan : Monotone doubleParam_jordan := by
  intro s t hst
  exact Subtype.coe_le_coe.mp (mul_le_mul_of_nonneg_left hst (by norm_num))

private lemma surjective_doubleParam_jordan : Function.Surjective doubleParam_jordan := by
  intro t
  refine ⟨⟨(t : ℝ) / 2, by constructor <;> nlinarith [t.property.1, t.property.2]⟩, ?_⟩
  apply Subtype.ext
  change 2 * ((t : ℝ) / 2) = t
  ring

private def reparamTwoToUnit_jordan (q : ContinuousBVPaths 0 2) :
    ContinuousBVPaths 0 1 :=
  ⟨q.val ∘ doubleParam_jordan,
    q.property.1.comp continuous_doubleParam_jordan,
    fun i ↦ BoundedVariationOn.comp_monotone_surjective_Icc (by norm_num)
      (q.property.2 i) monotone_doubleParam_jordan surjective_doubleParam_jordan⟩

private lemma reparamTwoToUnit_one (q : ContinuousBVPaths 0 2) :
    (reparamTwoToUnit_jordan q).val ⟨1, by norm_num⟩ = q.val ⟨2, by norm_num⟩ := by
  change q.val (doubleParam_jordan ⟨1, by norm_num⟩) = q.val ⟨2, by norm_num⟩
  rw [show doubleParam_jordan ⟨1, by norm_num⟩ = ⟨2, by norm_num⟩ by
    apply Subtype.ext
    norm_num [doubleParam_jordan]]

private def concatThreeUnitPaths_jordan (p₀ p₁ p₂ : ContinuousBVPaths 0 1)
    (h01 : p₀.val ⟨1, by norm_num⟩ = p₁.val ⟨0, by norm_num⟩)
    (h12 : p₁.val ⟨1, by norm_num⟩ = p₂.val ⟨0, by norm_num⟩) :
    ContinuousBVPaths 0 2 :=
  let q := concatUnitPaths_jordan p₀ p₁ h01
  concatUnitPaths_jordan (reparamTwoToUnit_jordan q) p₂ (by
    rw [reparamTwoToUnit_one]
    exact (concatUnitPaths_jordan_end p₀ p₁ h01).trans h12)

private lemma concatThreeUnitPaths_first_jordan
    (p₀ p₁ p₂ : ContinuousBVPaths 0 1)
    (h01 : p₀.val ⟨1, by norm_num⟩ = p₁.val ⟨0, by norm_num⟩)
    (h12 : p₁.val ⟨1, by norm_num⟩ = p₂.val ⟨0, by norm_num⟩)
    (t : Set.Icc (0 : ℝ) 1) :
    (concatThreeUnitPaths_jordan p₀ p₁ p₂ h01 h12).val
      ⟨(t : ℝ) / 2, by constructor <;> nlinarith [t.property.1, t.property.2]⟩ =
        p₀.val t := by
  simp only [concatThreeUnitPaths_jordan, concatUnitPaths_jordan,
    reparamTwoToUnit_jordan]
  unfold Function.concatUnitIntervals
  rw [ite_eq_left (by nlinarith [t.property.1, t.property.2] : (t : ℝ) / 2 ≤ 1)]
  have houter : Set.projIcc 0 1 (by norm_num) ((t : ℝ) / 2) =
      ⟨(t : ℝ) / 2, by constructor <;> nlinarith [t.property.1, t.property.2]⟩ := by
    exact Set.projIcc_of_mem (by norm_num) (by
      constructor <;> nlinarith [t.property.1, t.property.2])
  rw [houter]
  change Function.concatUnitIntervals p₀.val p₁.val
    (doubleParam_jordan ⟨(t : ℝ) / 2, by
      constructor <;> nlinarith [t.property.1, t.property.2]⟩) = p₀.val t
  rw [show doubleParam_jordan ⟨(t : ℝ) / 2, by
      constructor <;> nlinarith [t.property.1, t.property.2]⟩ =
      ⟨(t : ℝ), ⟨t.property.1, t.property.2.trans (by norm_num)⟩⟩ by
    apply Subtype.ext
    simp [doubleParam_jordan]
    ring]
  unfold Function.concatUnitIntervals
  rw [ite_eq_left t.property.2]
  apply congrArg p₀.val
  exact Set.projIcc_of_mem (by norm_num) t.property

private lemma concatThreeUnitPaths_middle_jordan
    (p₀ p₁ p₂ : ContinuousBVPaths 0 1)
    (h01 : p₀.val ⟨1, by norm_num⟩ = p₁.val ⟨0, by norm_num⟩)
    (h12 : p₁.val ⟨1, by norm_num⟩ = p₂.val ⟨0, by norm_num⟩)
    (t : Set.Icc (0 : ℝ) 1) :
    (concatThreeUnitPaths_jordan p₀ p₁ p₂ h01 h12).val
      ⟨(1 + (t : ℝ)) / 2, by
        constructor <;> nlinarith [t.property.1, t.property.2]⟩ = p₁.val t := by
  simp only [concatThreeUnitPaths_jordan, concatUnitPaths_jordan,
    reparamTwoToUnit_jordan]
  unfold Function.concatUnitIntervals
  rw [ite_eq_left (by nlinarith [t.property.2] : (1 + (t : ℝ)) / 2 ≤ 1)]
  have houter : Set.projIcc 0 1 (by norm_num) ((1 + (t : ℝ)) / 2) =
      ⟨(1 + (t : ℝ)) / 2, by
        constructor <;> nlinarith [t.property.1, t.property.2]⟩ := by
    exact Set.projIcc_of_mem (by norm_num) (by
      constructor <;> nlinarith [t.property.1, t.property.2])
  rw [houter]
  change Function.concatUnitIntervals p₀.val p₁.val
    (doubleParam_jordan ⟨(1 + (t : ℝ)) / 2, by
      constructor <;> nlinarith [t.property.1, t.property.2]⟩) = p₁.val t
  rw [show doubleParam_jordan ⟨(1 + (t : ℝ)) / 2, by
      constructor <;> nlinarith [t.property.1, t.property.2]⟩ =
      ⟨1 + (t : ℝ), by
        constructor <;> nlinarith [t.property.1, t.property.2]⟩ by
    apply Subtype.ext
    simp [doubleParam_jordan]
    ring]
  unfold Function.concatUnitIntervals
  by_cases ht : (t : ℝ) = 0
  · have ht' : t = ⟨0, by norm_num⟩ := Subtype.ext ht
    subst t
    simpa using h01
  · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
    rw [ite_eq_right (by linarith : ¬(1 + (t : ℝ) ≤ 1))]
    apply congrArg p₁.val
    apply Subtype.ext
    simp only [Set.coe_projIcc]
    rw [show 1 + (t : ℝ) - 1 = t by ring, min_eq_right t.property.2,
      max_eq_right t.property.1]

private lemma concatThreeUnitPaths_last_jordan
    (p₀ p₁ p₂ : ContinuousBVPaths 0 1)
    (h01 : p₀.val ⟨1, by norm_num⟩ = p₁.val ⟨0, by norm_num⟩)
    (h12 : p₁.val ⟨1, by norm_num⟩ = p₂.val ⟨0, by norm_num⟩)
    (t : Set.Icc (0 : ℝ) 1) :
    (concatThreeUnitPaths_jordan p₀ p₁ p₂ h01 h12).val
      ⟨1 + (t : ℝ), by
        constructor <;> nlinarith [t.property.1, t.property.2]⟩ = p₂.val t := by
  by_cases ht : (t : ℝ) = 0
  · have ht' : t = ⟨0, by norm_num⟩ := Subtype.ext ht
    rw [ht']
    rw [show (⟨1 + ((⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1) : ℝ), by
      norm_num⟩ : Set.Icc (0 : ℝ) 2) = ⟨1, by norm_num⟩ by
      apply Subtype.ext
      norm_num]
    change (concatThreeUnitPaths_jordan p₀ p₁ p₂ h01 h12).val
      ⟨1, by norm_num⟩ = p₂.val ⟨0, by norm_num⟩
    unfold concatThreeUnitPaths_jordan
    change Function.concatUnitIntervals _ p₂.val ⟨1, by norm_num⟩ = _
    unfold Function.concatUnitIntervals
    rw [ite_eq_left (by norm_num : (1 : ℝ) ≤ 1)]
    calc
      _ = (reparamTwoToUnit_jordan
          (concatUnitPaths_jordan p₀ p₁ h01)).val ⟨1, by norm_num⟩ := by
        apply congrArg _
        apply Subtype.ext
        norm_num [Set.coe_projIcc]
      _ = _ := by
        rw [reparamTwoToUnit_one, concatUnitPaths_jordan_end]
        exact h12
  · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
    simp only [concatThreeUnitPaths_jordan, concatUnitPaths_jordan]
    unfold Function.concatUnitIntervals
    rw [ite_eq_right (by linarith : ¬(1 + (t : ℝ) ≤ 1))]
    apply congrArg p₂.val
    apply Subtype.ext
    simp only [Set.coe_projIcc]
    rw [show 1 + (t : ℝ) - 1 = t by ring, min_eq_right t.property.2,
      max_eq_right t.property.1]

private theorem isPathConcatenation_concatThreeUnitPaths_jordan
    (p₀ p₁ p₂ : ContinuousBVPaths 0 1)
    (h01 : p₀.val ⟨1, by norm_num⟩ = p₁.val ⟨0, by norm_num⟩)
    (h12 : p₁.val ⟨1, by norm_num⟩ = p₂.val ⟨0, by norm_num⟩) :
    IsPathConcatenation
      { a := 0, b := 2, ordered := by norm_num,
        path := concatThreeUnitPaths_jordan p₀ p₁ p₂ h01 h12 }
      ![{ a := 0, b := 1, ordered := by norm_num, path := p₀ },
        { a := 0, b := 1, ordered := by norm_num, path := p₁ },
        { a := 0, b := 1, ordered := by norm_num, path := p₂ }] := by
  let cuts : Fin 4 → Set.Icc (0 : ℝ) 2 :=
    ![⟨0, by norm_num⟩, ⟨1 / 2, by norm_num⟩,
      ⟨1, by norm_num⟩, ⟨2, by norm_num⟩]
  refine ⟨by norm_num, cuts, ?_, rfl, rfl, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      norm_num [cuts, Matrix.cons_val_zero, Matrix.cons_val_one] at hij <;>
      norm_num [cuts, Matrix.cons_val_zero, Matrix.cons_val_one]
  intro i
  fin_cases i
  · let φ : Set.Icc (0 : ℝ) 1 → Set.Icc (cuts (Fin.castSucc 0) : ℝ)
        (cuts (Fin.succ 0) : ℝ) := fun t ↦ ⟨(t : ℝ) / 2, by
          change (0 : ℝ) ≤ (t : ℝ) / 2 ∧ (t : ℝ) / 2 ≤ 1 / 2
          constructor <;> nlinarith [t.property.1, t.property.2]⟩
    refine ⟨φ, id, Continuous.subtype_mk (continuous_subtype_val.div_const 2) _,
      ?_, ?_, continuous_id, monotone_id, Function.surjective_id, ?_⟩
    · intro s t hst
      exact Subtype.coe_le_coe.mp (div_le_div_of_nonneg_right hst (by norm_num))
    · intro t
      have ht : (0 : ℝ) ≤ t ∧ (t : ℝ) ≤ 1 / 2 := by
        simpa [cuts, Matrix.cons_val_zero, Matrix.cons_val_one] using t.property
      refine ⟨⟨2 * (t : ℝ), by
        change (0 : ℝ) ≤ 2 * (t : ℝ) ∧ 2 * (t : ℝ) ≤ 1
        constructor <;> nlinarith [ht.1, ht.2]⟩, ?_⟩
      apply Subtype.ext
      change 2 * (t : ℝ) / 2 = t
      ring
    · intro t
      exact concatThreeUnitPaths_first_jordan p₀ p₁ p₂ h01 h12 t
  · let φ : Set.Icc (0 : ℝ) 1 → Set.Icc (cuts (Fin.castSucc 1) : ℝ)
        (cuts (Fin.succ 1) : ℝ) := fun t ↦ ⟨(1 + (t : ℝ)) / 2, by
          change (1 / 2 : ℝ) ≤ (1 + (t : ℝ)) / 2 ∧ (1 + (t : ℝ)) / 2 ≤ 1
          constructor <;> nlinarith [t.property.1, t.property.2]⟩
    refine ⟨φ, id, Continuous.subtype_mk
      ((continuous_const.add continuous_subtype_val).div_const 2) _, ?_, ?_,
      continuous_id, monotone_id, Function.surjective_id, ?_⟩
    · intro s t hst
      apply Subtype.coe_le_coe.mp
      have hst' : (s : ℝ) ≤ t := hst
      change (1 + (s : ℝ)) / 2 ≤ (1 + (t : ℝ)) / 2
      linarith
    · intro t
      have ht : (1 / 2 : ℝ) ≤ t ∧ (t : ℝ) ≤ 1 := by
        simpa [cuts, Matrix.cons_val_zero, Matrix.cons_val_one] using t.property
      refine ⟨⟨2 * (t : ℝ) - 1, by
        change (0 : ℝ) ≤ 2 * (t : ℝ) - 1 ∧ 2 * (t : ℝ) - 1 ≤ 1
        constructor <;> nlinarith [ht.1, ht.2]⟩, ?_⟩
      apply Subtype.ext
      change (1 + (2 * (t : ℝ) - 1)) / 2 = t
      ring
    · intro t
      exact concatThreeUnitPaths_middle_jordan p₀ p₁ p₂ h01 h12 t
  · let φ : Set.Icc (0 : ℝ) 1 → Set.Icc (cuts (Fin.castSucc 2) : ℝ)
        (cuts (Fin.succ 2) : ℝ) := fun t ↦ ⟨1 + (t : ℝ), by
          change (1 : ℝ) ≤ 1 + (t : ℝ) ∧ 1 + (t : ℝ) ≤ 2
          constructor <;> nlinarith [t.property.1, t.property.2]⟩
    refine ⟨φ, id, Continuous.subtype_mk
      (continuous_const.add continuous_subtype_val) _, ?_, ?_,
      continuous_id, monotone_id, Function.surjective_id, ?_⟩
    · intro s t hst
      apply Subtype.coe_le_coe.mp
      have hst' : (s : ℝ) ≤ t := hst
      change 1 + (s : ℝ) ≤ 1 + (t : ℝ)
      linarith
    · intro t
      have ht : (1 : ℝ) ≤ t ∧ (t : ℝ) ≤ 2 := by
        simpa [cuts, Matrix.cons_val_zero, Matrix.cons_val_one] using t.property
      refine ⟨⟨(t : ℝ) - 1, by
        change (0 : ℝ) ≤ (t : ℝ) - 1 ∧ (t : ℝ) - 1 ≤ 1
        constructor <;> nlinarith [ht.1, ht.2]⟩, ?_⟩
      apply Subtype.ext
      change 1 + ((t : ℝ) - 1) = t
      ring
    · intro t
      exact concatThreeUnitPaths_last_jordan p₀ p₁ p₂ h01 h12 t

private lemma range_comp_surjective {α β γ : Type*} (f : β → γ) (g : α → β)
    (hg : Function.Surjective g) : Set.range (f ∘ g) = Set.range f := by
  apply Set.Subset.antisymm
  · exact Set.range_comp_subset_range _ _
  · rintro y ⟨x, rfl⟩
    obtain ⟨z, rfl⟩ := hg x
    exact ⟨z, rfl⟩

private lemma range_concatThreeUnitPaths_jordan
    (p₀ p₁ p₂ : ContinuousBVPaths 0 1)
    (h01 : p₀.val ⟨1, by norm_num⟩ = p₁.val ⟨0, by norm_num⟩)
    (h12 : p₁.val ⟨1, by norm_num⟩ = p₂.val ⟨0, by norm_num⟩) :
    Set.range (concatThreeUnitPaths_jordan p₀ p₁ p₂ h01 h12).val =
      Set.range p₀.val ∪ Set.range p₁.val ∪ Set.range p₂.val := by
  let q := concatUnitPaths_jordan p₀ p₁ h01
  have hqend : q.val ⟨2, by norm_num⟩ = p₂.val ⟨0, by norm_num⟩ :=
    (concatUnitPaths_jordan_end p₀ p₁ h01).trans h12
  have houter : (reparamTwoToUnit_jordan q).val ⟨1, by norm_num⟩ =
      p₂.val ⟨0, by norm_num⟩ := (reparamTwoToUnit_one q).trans hqend
  change Set.range (Function.concatUnitIntervals
    (reparamTwoToUnit_jordan q).val p₂.val) = _
  rw [Function.range_concatUnitIntervals _ _ houter]
  have hrepr : Set.range (reparamTwoToUnit_jordan q).val = Set.range q.val := by
    exact range_comp_surjective q.val doubleParam_jordan surjective_doubleParam_jordan
  rw [hrepr]
  change Set.range (Function.concatUnitIntervals p₀.val p₁.val) ∪ Set.range p₂.val = _
  rw [Function.range_concatUnitIntervals _ _ h01]

private lemma range_reverseArcUnitPath {A : OrientedJordanArc}
    (p : ArcBVParametrization A) (q : ContinuousBVPaths 0 1)
    (hq : q.val = (reverseArcPath p).val ∘ unitParam_jordan p.a p.b p.ordered) :
    Set.range q.val = A.carrier := by
  rw [hq, range_comp_surjective _ _ (surjective_unitParam_jordan _ _ _)]
  change Set.range (p.path.val ∘ Set.Icc.reverse p.ordered) = _
  rw [range_comp_surjective _ _ (Set.Icc.surjective_reverse p.ordered), p.range_eq]

private theorem segment_fst_supportingIntersection_inter_body
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (hne : (edgeVertices K (a : Real.Angle)).1 ≠
      (edgeVertices K (b : Real.Angle)).2) :
    segment ℝ (edgeVertices K (a : Real.Angle)).1 (supportingIntersection K a b) ∩
        (K : Set Point) = {(edgeVertices K (a : Real.Angle)).1} := by
  let P := (edgeVertices K (a : Real.Angle)).1
  let O := supportingIntersection K (a : Real.Angle) (b : Real.Angle)
  obtain ⟨d, hd, hO⟩ := supportingIntersection_eq_fst_add_pos_tangent K hab hba hne
  change O = P + d • tangentVector (a : Real.Angle) at hO
  apply Set.Subset.antisymm
  · rintro z ⟨hzseg, hzK⟩
    rw [segment_eq_image] at hzseg
    obtain ⟨r, hr, rfl⟩ := hzseg
    have hPn := (edgeVertices_fst_mem K (a : Real.Angle)).2
    have hOn := supportingIntersection_inner_left K a b
    have hzline : inner ℝ ((1 - r) • P + r • O) (normalVector (a : Real.Angle)) =
        supportValue K a := by
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
      change (1 - r) * inner ℝ P (normalVector (a : Real.Angle)) +
        r * inner ℝ O (normalVector (a : Real.Angle)) = _
      rw [show inner ℝ P (normalVector (a : Real.Angle)) = supportValue K a from hPn,
        show inner ℝ O (normalVector (a : Real.Angle)) = supportValue K a from hOn]
      ring
    have hzedge : (1 - r) • P + r • O ∈ exposedEdge K (a : Real.Angle) :=
      ⟨hzK, hzline⟩
    have hzle : inner ℝ ((1 - r) • P + r • O) (tangentVector (a : Real.Angle)) ≤
        inner ℝ P (tangentVector (a : Real.Angle)) := by
      rw [inner_edgeVertices_fst_tangent]
      exact le_csSup ((isCompact_exposedEdge K _).image
        (continuous_id.inner continuous_const)).bddAbove ⟨_, hzedge, rfl⟩
    rw [hO, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      inner_add_left, real_inner_smul_left, inner_tangentVector_self] at hzle
    have hr0 : r = 0 := by nlinarith [hr.1]
    simp [hr0]
  · intro z hz
    have hzP : z = P := by simpa [P] using hz
    subst z
    exact ⟨left_mem_segment ℝ P O, (edgeVertices_fst_mem K _).1⟩

private theorem segment_supportingIntersection_snd_inter_body
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (hne : (edgeVertices K (a : Real.Angle)).1 ≠
      (edgeVertices K (b : Real.Angle)).2) :
    segment ℝ (supportingIntersection K a b) (edgeVertices K (b : Real.Angle)).2 ∩
        (K : Set Point) = {(edgeVertices K (b : Real.Angle)).2} := by
  let Q := (edgeVertices K (b : Real.Angle)).2
  let O := supportingIntersection K (a : Real.Angle) (b : Real.Angle)
  obtain ⟨d, hd, hO⟩ := supportingIntersection_eq_snd_sub_pos_tangent K hab hba hne
  change O = Q - d • tangentVector (b : Real.Angle) at hO
  apply Set.Subset.antisymm
  · rintro z ⟨hzseg, hzK⟩
    rw [segment_eq_image] at hzseg
    obtain ⟨r, hr, rfl⟩ := hzseg
    have hQn := (edgeVertices_snd_mem K (b : Real.Angle)).2
    have hOn := supportingIntersection_inner_right K a b
      (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hab) (by linarith)).ne'
    have hzline : inner ℝ ((1 - r) • O + r • Q) (normalVector (b : Real.Angle)) =
        supportValue K b := by
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
      change (1 - r) * inner ℝ O (normalVector (b : Real.Angle)) +
        r * inner ℝ Q (normalVector (b : Real.Angle)) = _
      rw [show inner ℝ O (normalVector (b : Real.Angle)) = supportValue K b from hOn,
        show inner ℝ Q (normalVector (b : Real.Angle)) = supportValue K b from hQn]
      ring
    have hzedge : (1 - r) • O + r • Q ∈ exposedEdge K (b : Real.Angle) :=
      ⟨hzK, hzline⟩
    have hzge : inner ℝ Q (tangentVector (b : Real.Angle)) ≤
        inner ℝ ((1 - r) • O + r • Q) (tangentVector (b : Real.Angle)) := by
      rw [inner_edgeVertices_snd_tangent]
      exact csInf_le ((isCompact_exposedEdge K _).image
        (continuous_id.inner continuous_const)).bddBelow ⟨_, hzedge, rfl⟩
    rw [hO, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      inner_sub_left, real_inner_smul_left, inner_tangentVector_self] at hzge
    have hr1 : r = 1 := by nlinarith [hr.2]
    simp [hr1]
  · intro z hz
    have hzQ : z = Q := by simpa [Q] using hz
    subst z
    exact ⟨right_mem_segment ℝ O Q, (edgeVertices_snd_mem K _).1⟩

/-- A convex boundary arc lies in its convex body. -/
theorem convexBoundaryArc_subset_body (K : ConvexBody Point) (a b : ℝ) :
    convexBoundaryArc K a b ⊆ (K : Set Point) := by
  rintro z (hz | hz)
  · rcases hz with hz | hz
    · simpa using hz ▸ (edgeVertices_fst_mem K (a : Real.Angle)).1
    · rcases Set.mem_iUnion.mp hz with ⟨t, hz⟩
      rcases Set.mem_iUnion.mp hz with ⟨_, hz⟩
      exact hz.1
  · simpa using hz ▸ (edgeVertices_snd_mem K (b : Real.Angle)).1

private theorem segment_fst_inter_convexBoundaryArc
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (hne : (edgeVertices K (a : Real.Angle)).1 ≠
      (edgeVertices K (b : Real.Angle)).2) :
    segment ℝ (edgeVertices K (a : Real.Angle)).1 (supportingIntersection K a b) ∩
        convexBoundaryArc K a b = {(edgeVertices K (a : Real.Angle)).1} := by
  apply Set.Subset.antisymm
  · intro z hz
    have hz' : z ∈ segment ℝ (edgeVertices K (a : Real.Angle)).1
        (supportingIntersection K a b) ∩ (K : Set Point) :=
      ⟨hz.1, convexBoundaryArc_subset_body K a b hz.2⟩
    simpa [segment_fst_supportingIntersection_inter_body K hab hba hne] using hz'
  · intro z hz
    have hzP : z = (edgeVertices K (a : Real.Angle)).1 := by simpa using hz
    subst z
    exact ⟨left_mem_segment _ _ _, Or.inl (Or.inl rfl)⟩

private theorem segment_snd_inter_convexBoundaryArc
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (hne : (edgeVertices K (a : Real.Angle)).1 ≠
      (edgeVertices K (b : Real.Angle)).2) :
    segment ℝ (supportingIntersection K a b) (edgeVertices K (b : Real.Angle)).2 ∩
        convexBoundaryArc K a b = {(edgeVertices K (b : Real.Angle)).2} := by
  apply Set.Subset.antisymm
  · intro z hz
    have hz' : z ∈ segment ℝ (supportingIntersection K a b)
        (edgeVertices K (b : Real.Angle)).2 ∩ (K : Set Point) :=
      ⟨hz.1, convexBoundaryArc_subset_body K a b hz.2⟩
    simpa [segment_supportingIntersection_snd_inter_body K hab hba hne] using hz'
  · intro z hz
    have hzQ : z = (edgeVertices K (b : Real.Angle)).2 := by simpa using hz
    subst z
    exact ⟨right_mem_segment _ _ _, Or.inr rfl⟩

private theorem supporting_segments_inter
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi) :
    segment ℝ (edgeVertices K (a : Real.Angle)).1 (supportingIntersection K a b) ∩
      segment ℝ (supportingIntersection K a b) (edgeVertices K (b : Real.Angle)).2 =
        {supportingIntersection K a b} := by
  let P := (edgeVertices K (a : Real.Angle)).1
  let Q := (edgeVertices K (b : Real.Angle)).2
  let O := supportingIntersection K (a : Real.Angle) (b : Real.Angle)
  have hsin : 0 < Real.sin (b - a) :=
    Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hab) (by linarith)
  have hPa : inner ℝ P (normalVector (a : Real.Angle)) = supportValue K a :=
    (edgeVertices_fst_mem K _).2
  have hOa : inner ℝ O (normalVector (a : Real.Angle)) = supportValue K a :=
    supportingIntersection_inner_left K a b
  have hOb : inner ℝ O (normalVector (b : Real.Angle)) = supportValue K b :=
    supportingIntersection_inner_right K a b hsin.ne'
  have hQb : inner ℝ Q (normalVector (b : Real.Angle)) = supportValue K b :=
    (edgeVertices_snd_mem K _).2
  have inner_eq_of_segment {X Y z v : Point} {c : ℝ}
      (hX : inner ℝ X v = c) (hY : inner ℝ Y v = c)
      (hz : z ∈ segment ℝ X Y) : inner ℝ z v = c := by
    rw [segment_eq_image] at hz
    obtain ⟨r, hr, rfl⟩ := hz
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, hX, hY]
    ring
  apply Set.Subset.antisymm
  · rintro z ⟨hz₁, hz₂⟩
    have hza : inner ℝ z (normalVector (a : Real.Angle)) = supportValue K a :=
      inner_eq_of_segment hPa hOa hz₁
    have hzb : inner ℝ z (normalVector (b : Real.Angle)) = supportValue K b :=
      inner_eq_of_segment hOb hQb hz₂
    have hna : inner ℝ (z - O) (normalVector (a : Real.Angle)) = 0 := by
      rw [inner_sub_left, hza, hOa, sub_self]
    have hnb : inner ℝ (z - O) (normalVector (b : Real.Angle)) = 0 := by
      rw [inner_sub_left, hzb, hOb, sub_self]
    have hnexp : normalVector (b : Real.Angle) =
        Real.cos (b - a) • normalVector (a : Real.Angle) +
          Real.sin (b - a) • tangentVector (a : Real.Angle) := by
      simpa only [add_sub_cancel] using normalVector_add_real a (b - a)
    have hta : inner ℝ (z - O) (tangentVector (a : Real.Angle)) = 0 := by
      rw [hnexp, inner_add_right, inner_smul_right, inner_smul_right, hna,
        mul_zero, zero_add] at hnb
      exact (mul_eq_zero.mp hnb).resolve_left hsin.ne'
    have hzo : z = O := by
      rw [show z = O + (z - O) by abel, ← inner_normalVector_smul_add_inner_tangentVector_smul
        (z - O) (a : Real.Angle), hna, hta, zero_smul, zero_smul, add_zero]
      simp
    simp [O, hzo]
  · intro z hz
    have hzO : z = O := by simpa [O] using hz
    subst z
    exact ⟨right_mem_segment _ _ _, left_mem_segment _ _ _⟩

private def brokenSupportPath (K : ConvexBody Point) (a b : ℝ) :
    Path (edgeVertices K (a : Real.Angle)).1 (edgeVertices K (b : Real.Angle)).2 :=
  (Path.segment (edgeVertices K (a : Real.Angle)).1 (supportingIntersection K a b)).trans
    (Path.segment (supportingIntersection K a b) (edgeVertices K (b : Real.Angle)).2)

private theorem path_segment_injective {P Q : Point} (hPQ : P ≠ Q) :
    Function.Injective (Path.segment P Q) := by
  intro s t hst
  apply Subtype.ext
  exact AffineMap.lineMap_injective ℝ hPQ (by
    simpa only [Path.segment_apply] using hst)

private theorem brokenSupportPath_injective
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (hne : (edgeVertices K (a : Real.Angle)).1 ≠
      (edgeVertices K (b : Real.Angle)).2) :
    Function.Injective (brokenSupportPath K a b) := by
  let P := (edgeVertices K (a : Real.Angle)).1
  let Q := (edgeVertices K (b : Real.Angle)).2
  let O := supportingIntersection K (a : Real.Angle) (b : Real.Angle)
  obtain ⟨d₀, hd₀, hPO⟩ := supportingIntersection_eq_fst_add_pos_tangent K hab hba hne
  obtain ⟨d₁, hd₁, hQO⟩ := supportingIntersection_eq_snd_sub_pos_tangent K hab hba hne
  change O = P + d₀ • tangentVector (a : Real.Angle) at hPO
  change O = Q - d₁ • tangentVector (b : Real.Angle) at hQO
  have htne (u : Real.Angle) : tangentVector u ≠ 0 := by
    intro hu
    have hone : inner ℝ (tangentVector u) (tangentVector u) = 1 := by
      rw [← u.coe_toReal]
      exact inner_tangentVector_self u.toReal
    rw [hu] at hone
    simp at hone
  have hPOne : P ≠ O := by
    intro h
    have hz : d₀ • tangentVector (a : Real.Angle) = 0 := by
      calc
        d₀ • tangentVector (a : Real.Angle) = O - P := by rw [hPO]; abel
        _ = 0 := by rw [← h, sub_self]
    exact hd₀.ne' ((smul_eq_zero.mp hz).resolve_right (htne _))
  have hOQne : O ≠ Q := by
    intro h
    have hz : d₁ • tangentVector (b : Real.Angle) = 0 := by
      calc
        d₁ • tangentVector (b : Real.Angle) = Q - O := by rw [hQO]; abel
        _ = 0 := by rw [h, sub_self]
    exact hd₁.ne' ((smul_eq_zero.mp hz).resolve_right (htne _))
  intro s t hst
  change ((Path.segment P O).trans (Path.segment O Q)) s =
    ((Path.segment P O).trans (Path.segment O Q)) t at hst
  simp only [Path.trans_apply] at hst
  split_ifs at hst with hs ht ht
  · have heq := path_segment_injective hPOne hst
    apply Subtype.ext
    have := congrArg Subtype.val heq
    norm_num at this ⊢
    linarith

  · have hmem : (Path.segment P O) ⟨2 * (s : ℝ), by constructor <;> linarith
        [s.property.1, s.property.2]⟩ ∈ segment ℝ P O ∩ segment ℝ O Q := by
      constructor
      · rw [← Path.range_segment]
        exact Set.mem_range_self _
      · rw [hst, ← Path.range_segment]
        exact Set.mem_range_self _
    have hO := Set.ext_iff.mp (supporting_segments_inter K hab hba) _ |>.mp hmem
    have hs1 : (2 : ℝ) * s = 1 := by
      have heq := path_segment_injective hPOne (hO.trans (Path.target _).symm)
      exact congrArg Subtype.val heq
    have ht0 : 2 * (t : ℝ) - 1 = 0 := by
      have heq := path_segment_injective hOQne (hst.symm.trans (hO.trans (Path.source _).symm))
      exact congrArg Subtype.val heq
    apply Subtype.ext
    linarith
  · have hmem : (Path.segment P O) ⟨2 * (t : ℝ), by constructor <;> linarith
        [t.property.1, t.property.2]⟩ ∈ segment ℝ P O ∩ segment ℝ O Q := by
      constructor
      · rw [← Path.range_segment]
        exact Set.mem_range_self _
      · rw [← hst, ← Path.range_segment]
        exact Set.mem_range_self _
    have hO := Set.ext_iff.mp (supporting_segments_inter K hab hba) _ |>.mp hmem
    have ht1 : (2 : ℝ) * t = 1 := by
      have heq := path_segment_injective hPOne (hO.trans (Path.target _).symm)
      exact congrArg Subtype.val heq
    have hs0 : 2 * (s : ℝ) - 1 = 0 := by
      have heq := path_segment_injective hOQne (hst.trans (hO.trans (Path.source _).symm))
      exact congrArg Subtype.val heq
    apply Subtype.ext
    linarith
  · have heq := path_segment_injective hOQne hst
    apply Subtype.ext
    have := congrArg Subtype.val heq
    norm_num at this ⊢
    linarith

private theorem brokenSupportPath_range
    (K : ConvexBody Point) (a b : ℝ) :
    Set.range (brokenSupportPath K a b) =
      segment ℝ (edgeVertices K (a : Real.Angle)).1 (supportingIntersection K a b) ∪
      segment ℝ (supportingIntersection K a b) (edgeVertices K (b : Real.Angle)).2 := by
  simp [brokenSupportPath, Path.trans_range, Path.range_segment]

private theorem brokenSupportPath_range_inter_convexBoundaryArc
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (hne : (edgeVertices K (a : Real.Angle)).1 ≠
      (edgeVertices K (b : Real.Angle)).2) :
    Set.range (brokenSupportPath K a b) ∩ convexBoundaryArc K a b =
      {(edgeVertices K (a : Real.Angle)).1, (edgeVertices K (b : Real.Angle)).2} := by
  rw [brokenSupportPath_range, Set.union_inter_distrib_right,
    segment_fst_inter_convexBoundaryArc K hab hba hne,
    segment_snd_inter_convexBoundaryArc K hab hba hne]
  ext z
  simp [or_comm]

private def arcUnitPath {A : OrientedJordanArc} (p : ArcBVParametrization A) :
    Path A.startPoint A.endPoint where
  toFun := p.path.val ∘ unitParam_jordan p.a p.b p.ordered
  source' := by
    change p.path.val (unitParam_jordan p.a p.b p.ordered 0) = A.startPoint
    rw [show unitParam_jordan p.a p.b p.ordered 0 = ⟨p.a, le_rfl, p.ordered⟩ by
      exact Set.Icc.convexComb_zero _ _]
    exact p.start_eq
  target' := by
    change p.path.val (unitParam_jordan p.a p.b p.ordered 1) = A.endPoint
    rw [show unitParam_jordan p.a p.b p.ordered 1 = ⟨p.b, p.ordered, le_rfl⟩ by
      exact Set.Icc.convexComb_one _ _]
    exact p.end_eq
  continuous_toFun := p.path.property.1.comp (continuous_unitParam_jordan _ _ _)

private theorem arcUnitPath_injective {A : OrientedJordanArc}
    (p : ArcBVParametrization A) (hne : A.startPoint ≠ A.endPoint) :
    Function.Injective (arcUnitPath p) := by
  intro s t hst
  have hpab : p.a < p.b := lt_of_le_of_ne p.ordered fun hab ↦ by
    have heq : (⟨p.a, le_rfl, p.ordered⟩ : Set.Icc p.a p.b) =
        ⟨p.b, p.ordered, le_rfl⟩ := Subtype.ext hab
    exact hne (p.start_eq.symm.trans ((congrArg p.path.val heq).trans p.end_eq))
  have huv := p.injective (by simpa [arcUnitPath, Function.comp_apply] using hst)
  exact (strictMono_convexComb_of_lt _ _ hpab).injective huv

private theorem arcUnitPath_range {A : OrientedJordanArc}
    (p : ArcBVParametrization A) : Set.range (arcUnitPath p) = A.carrier := by
  change Set.range (p.path.val ∘ unitParam_jordan p.a p.b p.ordered) = _
  rw [range_comp_surjective _ _ (surjective_unitParam_jordan _ _ _), p.range_eq]

private theorem isJordanCurve_of_tau {Γ : Set Point} (hΓ : TauCeti.IsJordanCurve Γ) :
    IsJordanCurve Γ := by
  obtain ⟨e⟩ := hΓ
  refine ⟨fun z ↦ (e.symm z : Point), continuous_subtype_val.comp e.symm.continuous,
    fun z w h ↦ e.symm.injective (Subtype.ext h), ?_⟩
  apply Set.Subset.antisymm
  · rintro z ⟨u, rfl⟩
    exact (e.symm u).property
  · intro z hz
    exact ⟨e ⟨z, hz⟩, congrArg Subtype.val (e.symm_apply_apply ⟨z, hz⟩)⟩

private theorem convexArc_broken_isJordanCurve
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (hne : (edgeVertices K (a : Real.Angle)).1 ≠
      (edgeVertices K (b : Real.Angle)).2)
    (A : RectifiableOrientedArc) (p : ArcBVParametrization A.val)
    (hA : RealizesConvexArc K a b A) :
    IsJordanCurve (Set.range (brokenSupportPath K a b) ∪ A.val.carrier) := by
  have hmeet : Set.range (brokenSupportPath K a b) ∩ Set.range (arcUnitPath p) =
      {(edgeVertices K (a : Real.Angle)).1, (edgeVertices K (b : Real.Angle)).2} := by
    rw [arcUnitPath_range, hA.1]
    exact brokenSupportPath_range_inter_convexBoundaryArc K hab hba hne
  have hstart : A.val.startPoint = (edgeVertices K (a : Real.Angle)).1 := hA.2.1
  have hend : A.val.endPoint = (edgeVertices K (b : Real.Angle)).2 := hA.2.2
  have hstartend : A.val.startPoint ≠ A.val.endPoint := by simpa [hstart, hend] using hne
  let δ : Path (edgeVertices K (a : Real.Angle)).1
      (edgeVertices K (b : Real.Angle)).2 :=
    (arcUnitPath p).cast hstart.symm hend.symm
  have hδinj : Function.Injective δ := by
    simpa only [δ, Path.cast_coe] using arcUnitPath_injective p hstartend
  have hδrange : Set.range δ = A.val.carrier := by
    simpa only [δ, Path.cast_coe] using arcUnitPath_range p
  have htau := TauCeti.isJordanCurve_range_union_range_of_inter_eq_pair
    (brokenSupportPath_injective K hab hba hne) hδinj (by
      rw [hδrange]
      simpa [hstart, hend, arcUnitPath_range] using hmeet)
  rw [hδrange] at htau
  exact isJordanCurve_of_tau htau

private theorem jordanInterior_subset_closedConvexHull {Γ : Set Point}
    (hΓ : Γ.Nonempty) : jordanInterior Γ ⊆ closedConvexHull ℝ Γ := by
  intro p hp
  exact TauCeti.filledHull_subset_closedConvexHull hΓ hp.2

/-- The region enclosed by a loop inside a closed convex set stays inside that set. -/
theorem jordanInterior_subset_of_subset_closed_convex
    {Γ C : Set Point} (hΓ : Γ.Nonempty) (hsub : Γ ⊆ C)
    (hconv : Convex ℝ C) (hclosed : IsClosed C) : jordanInterior Γ ⊆ C := by
  exact (jordanInterior_subset_closedConvexHull hΓ).trans
    (closedConvexHull_min hsub hconv hclosed)

private theorem isOpen_jordanInterior_of_isJordanCurve {Γ : Set Point}
    (hΓ : IsJordanCurve Γ) : IsOpen (jordanInterior Γ) := by
  obtain ⟨U, V, hUopen, hVopen, hUconn, hVconn, hUbounded, hVunbounded, hdis,
    hcover, hfrontU, hfrontV, hcompU, hcompV⟩ := jordan_separation hΓ
  have heq : jordanInterior Γ = U := by
    ext p
    constructor
    · intro hp
      have hpUV : p ∈ U ∪ V := hcover.symm.subset hp.1
      rcases hpUV with hpU | hpV
      · exact hpU
      · exfalso
        exact hVunbounded (by simpa only [hcompV p hpV] using hp.2)
    · intro hpU
      constructor
      · intro hpΓ
        have hpcompl : p ∈ Γᶜ := hcover ▸ Or.inl hpU
        exact hpcompl hpΓ
      · simpa only [hcompU p hpU] using hUbounded
  rw [heq]
  exact hUopen

private theorem jordanInterior_subset_interior_of_subset_closed_convex
    {Γ C : Set Point} (hJordan : IsJordanCurve Γ) (hΓ : Γ.Nonempty)
    (hsub : Γ ⊆ C) (hconv : Convex ℝ C) (hclosed : IsClosed C) :
    jordanInterior Γ ⊆ interior C := by
  intro p hp
  apply mem_interior_iff_mem_nhds.mpr
  exact Filter.mem_of_superset
    ((isOpen_jordanInterior_of_isJordanCurve hJordan).mem_nhds hp)
    (jordanInterior_subset_of_subset_closed_convex hΓ hsub hconv hclosed)

private theorem injOn_concatUnitPaths_jordan
    (p q : ContinuousBVPaths 0 1)
    (hjoin : p.val ⟨1, by norm_num⟩ = q.val ⟨0, by norm_num⟩)
    (hclose : q.val ⟨1, by norm_num⟩ = p.val ⟨0, by norm_num⟩)
    (hp : Function.Injective p.val) (hq : Function.Injective q.val)
    (hmeet : Set.range p.val ∩ Set.range q.val =
      {p.val ⟨0, by norm_num⟩, p.val ⟨1, by norm_num⟩}) :
    Set.InjOn (concatUnitPaths_jordan p q hjoin).val {t | (t : ℝ) < 2} := by
  intro s hs t ht hst
  change (s : ℝ) < 2 at hs
  change (t : ℝ) < 2 at ht
  change Function.concatUnitIntervals p.val q.val s =
    Function.concatUnitIntervals p.val q.val t at hst
  unfold Function.concatUnitIntervals at hst
  split_ifs at hst with hs₁ ht₁ ht₁
  · have heq := congrArg Subtype.val (hp hst)
    apply Subtype.ext
    simp only [Set.coe_projIcc] at heq
    rw [min_eq_right hs₁, max_eq_right s.property.1,
      min_eq_right ht₁, max_eq_right t.property.1] at heq
    exact heq
  · have hmem : p.val (Set.projIcc 0 1 (by norm_num) (s : ℝ)) ∈
        Set.range p.val ∩ Set.range q.val :=
      ⟨Set.mem_range_self _, hst ▸ Set.mem_range_self _⟩
    rw [hmeet] at hmem
    rcases hmem with hP | hQ
    · have hs0 := congrArg Subtype.val (hp hP)
      have ht1 := congrArg Subtype.val (hq (hst.symm.trans (hP.trans hclose.symm)))
      simp only [Set.coe_projIcc] at hs0 ht1
      rw [min_eq_right hs₁, max_eq_right s.property.1] at hs0
      rw [min_eq_right (by linarith [t.property.2]),
        max_eq_right (by linarith)] at ht1
      exfalso
      linarith
    · have hs1 := congrArg Subtype.val (hp hQ)
      have ht0 := congrArg Subtype.val (hq (hst.symm.trans (hQ.trans hjoin)))
      simp only [Set.coe_projIcc] at hs1 ht0
      rw [min_eq_right hs₁, max_eq_right s.property.1] at hs1
      rw [min_eq_right (by linarith [t.property.2]),
        max_eq_right (by linarith)] at ht0
      apply Subtype.ext
      linarith
  · have hmem : p.val (Set.projIcc 0 1 (by norm_num) (t : ℝ)) ∈
        Set.range p.val ∩ Set.range q.val :=
      ⟨Set.mem_range_self _, hst.symm ▸ Set.mem_range_self _⟩
    rw [hmeet] at hmem
    rcases hmem with hP | hQ
    · have ht0 := congrArg Subtype.val (hp hP)
      have hs1 := congrArg Subtype.val (hq (hst.trans (hP.trans hclose.symm)))
      simp only [Set.coe_projIcc] at ht0 hs1
      rw [min_eq_right ht₁, max_eq_right t.property.1] at ht0
      rw [min_eq_right (by linarith [s.property.2]),
        max_eq_right (by linarith)] at hs1
      exfalso
      linarith
    · have ht1 := congrArg Subtype.val (hp hQ)
      have hs0 := congrArg Subtype.val (hq (hst.trans (hQ.trans hjoin)))
      simp only [Set.coe_projIcc] at ht1 hs0
      rw [min_eq_right ht₁, max_eq_right t.property.1] at ht1
      rw [min_eq_right (by linarith [s.property.2]),
        max_eq_right (by linarith)] at hs0
      apply Subtype.ext
      linarith
  · have heq := congrArg Subtype.val (hq hst)
    apply Subtype.ext
    simp only [Set.coe_projIcc] at heq
    rw [min_eq_right (by linarith [s.property.2]), max_eq_right (by linarith),
      min_eq_right (by linarith [t.property.2]), max_eq_right (by linarith)] at heq
    linarith

private theorem reparam_support_segments_eq_brokenSupportPath
    (K : ConvexBody Point) (a b : ℝ)
    (h01 : (lineSegmentBVPath (edgeVertices K a).1 (supportingIntersection K a b)).val
      ⟨1, by norm_num⟩ =
      (lineSegmentBVPath (supportingIntersection K a b) (edgeVertices K b).2).val
        ⟨0, by norm_num⟩) :
    (reparamTwoToUnit_jordan (concatUnitPaths_jordan
      (lineSegmentBVPath (edgeVertices K a).1 (supportingIntersection K a b))
      (lineSegmentBVPath (supportingIntersection K a b) (edgeVertices K b).2)
      h01)).val = brokenSupportPath K a b := by
  funext t
  simp only [reparamTwoToUnit_jordan, Function.comp_apply, doubleParam_jordan,
    concatUnitPaths_jordan, lineSegmentBVPath, brokenSupportPath]
  by_cases ht : (t : ℝ) ≤ 1 / 2
  · simp only [Path.trans_apply, dite_eq_left ht]
    unfold Function.concatUnitIntervals
    rw [ite_eq_left (by linarith)]
    congr 1
    apply Subtype.ext
    simp only [Set.coe_projIcc]
    rw [min_eq_right (by linarith [t.property.2]),
      max_eq_right (by linarith [t.property.1])]
  · simp only [Path.trans_apply, dite_eq_right ht]
    unfold Function.concatUnitIntervals
    rw [ite_eq_right (by linarith)]
    congr 1
    apply Subtype.ext
    simp only [Set.coe_projIcc]
    rw [min_eq_right (by linarith [t.property.2]),
      max_eq_right (by linarith [t.property.1])]

private theorem reverseArcUnitPath_injective {A : OrientedJordanArc}
    (p : ArcBVParametrization A) (q : ContinuousBVPaths 0 1)
    (hq : q.val = (reverseArcPath p).val ∘ unitParam_jordan p.a p.b p.ordered)
    (hne : A.startPoint ≠ A.endPoint) : Function.Injective q.val := by
  have hpab : p.a < p.b := lt_of_le_of_ne p.ordered fun hab ↦ by
    have heq : (⟨p.a, le_rfl, p.ordered⟩ : Set.Icc p.a p.b) =
        ⟨p.b, p.ordered, le_rfl⟩ := Subtype.ext hab
    exact hne (p.start_eq.symm.trans ((congrArg p.path.val heq).trans p.end_eq))
  intro s t hst
  rw [hq] at hst
  have hrev := p.injective hst
  apply Subtype.ext
  have hval := congrArg Subtype.val hrev
  simp only [Set.Icc.reverse] at hval
  have huv : (unitParam_jordan p.a p.b p.ordered s : ℝ) =
      unitParam_jordan p.a p.b p.ordered t := by linarith
  exact congrArg Subtype.val
    ((strictMono_convexComb_of_lt _ _ hpab).injective (Subtype.ext huv))

private theorem brokenSupportPath_union_convexArc_subset_endpointHalfPlanes
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (A : RectifiableOrientedArc) (hA : RealizesConvexArc K a b A) :
    Set.range (brokenSupportPath K a b) ∪ A.val.carrier ⊆
      (supportingLineHalfPlane K (a : Real.Angle)).2 ∩
        (supportingLineHalfPlane K (b : Real.Angle)).2 := by
  have hsin : 0 < Real.sin (b - a) :=
    Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hab) (by linarith)
  have hK (t : Real.Angle) : (K : Set Point) ⊆ (supportingLineHalfPlane K t).2 := by
    intro p hp
    exact inner_le_supportValue K hp t
  have hOa : supportingIntersection K a b ∈ (supportingLineHalfPlane K a).2 := by
    exact le_of_eq (supportingIntersection_inner_left K a b)
  have hOb : supportingIntersection K a b ∈ (supportingLineHalfPlane K b).2 := by
    exact le_of_eq (supportingIntersection_inner_right K a b hsin.ne')
  have hconv (t : Real.Angle) : Convex ℝ (supportingLineHalfPlane K t).2 := by
    intro x hx y hy u v hu hv huv
    change inner ℝ x (normalVector t) ≤ supportValue K t at hx
    change inner ℝ y (normalVector t) ≤ supportValue K t at hy
    change inner ℝ (u • x + v • y) (normalVector t) ≤ supportValue K t
    rw [inner_add_left, inner_smul_left, inner_smul_left]
    simp only [RCLike.conj_to_real]
    calc
      u * inner ℝ x (normalVector t) + v * inner ℝ y (normalVector t) ≤
          u * supportValue K t + v * supportValue K t :=
        add_le_add (mul_le_mul_of_nonneg_left hx hu) (mul_le_mul_of_nonneg_left hy hv)
      _ = supportValue K t := by rw [← add_mul, huv, one_mul]
  intro p hp
  rcases hp with hp | hp
  · rw [brokenSupportPath_range] at hp
    rcases hp with hp | hp
    · constructor
      · exact (hconv a).segment_subset
          (hK a (edgeVertices_fst_mem K (a : Real.Angle)).1) hOa hp
      · exact (hconv b).segment_subset
          (hK b (edgeVertices_fst_mem K (a : Real.Angle)).1) hOb hp
    · constructor
      · exact (hconv a).segment_subset hOa
          (hK a (edgeVertices_snd_mem K (b : Real.Angle)).1) hp
      · exact (hconv b).segment_subset hOb
          (hK b (edgeVertices_snd_mem K (b : Real.Angle)).1) hp
  · have hpK : p ∈ K := convexBoundaryArc_subset_body K a b (hA.1 ▸ hp)
    exact ⟨hK a hpK, hK b hpK⟩

private theorem convexBoundaryArc_exists_support_eq
    (K : ConvexBody Point) {a b : ℝ} (hab : a ≤ b) {p : Point}
    (hp : p ∈ convexBoundaryArc K a b) :
    ∃ t ∈ Set.Icc a b,
      inner ℝ p (normalVector (t : Real.Angle)) = supportValue K (t : Real.Angle) := by
  rcases hp with (hp | hp) | hp
  · subst p
    exact ⟨a, ⟨le_rfl, hab⟩, (edgeVertices_fst_mem K (a : Real.Angle)).2⟩
  · simp only [Set.mem_iUnion] at hp
    obtain ⟨t, htab, hp⟩ := hp
    exact ⟨t, ⟨htab.1.le, htab.2.le⟩, hp.2⟩
  · subst p
    exact ⟨b, ⟨hab, le_rfl⟩, (edgeVertices_snd_mem K (b : Real.Angle)).2⟩

private theorem inner_midpoint_normal_pos {a b t : ℝ}
    (_hab : a < b) (hba : b < a + Real.pi) (ht : t ∈ Set.Icc a b) :
    0 < inner ℝ (normalVector (((a + b) / 2 : ℝ) : Real.Angle))
      (normalVector (t : Real.Angle)) := by
  rw [inner_normalVector_normalVector]
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [ht.1, ht.2]

private theorem sub_pos_midpoint_normal_inner_lt_support
    (K : ConvexBody Point) {a b r : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    {p : Point}
    (hp : p ∈ ⋂ t ∈ Set.Icc a b,
      (supportingLineHalfPlane K (t : Real.Angle)).2) (hr : 0 < r)
    (t : ℝ) (ht : t ∈ Set.Icc a b) :
    inner ℝ (p - r • normalVector (((a + b) / 2 : ℝ) : Real.Angle))
        (normalVector (t : Real.Angle)) < supportValue K (t : Real.Angle) := by
  have hple : inner ℝ p (normalVector (t : Real.Angle)) ≤
      supportValue K (t : Real.Angle) := by
    exact Set.mem_iInter₂.mp hp t ht
  rw [inner_sub_left, real_inner_smul_left]
  have hdot := inner_midpoint_normal_pos hab hba ht
  nlinarith

private theorem brokenSupportPath_mem_support_eq
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi) {p : Point}
    (hp : p ∈ Set.range (brokenSupportPath K a b)) :
    inner ℝ p (normalVector (a : Real.Angle)) = supportValue K a ∨
      inner ℝ p (normalVector (b : Real.Angle)) = supportValue K b := by
  have hsin : Real.sin (b - a) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hab) (by linarith)).ne'
  rw [brokenSupportPath_range] at hp
  rcases hp with hp | hp
  · left
    rw [segment_eq_image] at hp
    obtain ⟨r, hr, rfl⟩ := hp
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
      (edgeVertices_fst_mem K (a : Real.Angle)).2,
      supportingIntersection_inner_left]
    ring
  · right
    rw [segment_eq_image] at hp
    obtain ⟨r, hr, rfl⟩ := hp
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
      supportingIntersection_inner_right K a b hsin,
      (edgeVertices_snd_mem K (b : Real.Angle)).2]
    ring

private theorem sub_pos_midpoint_normal_not_mem_boundary_loop
    (K : ConvexBody Point) {a b r : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (A : RectifiableOrientedArc) (hA : RealizesConvexArc K a b A) {p : Point}
    (hp : p ∈ ⋂ t ∈ Set.Icc a b,
      (supportingLineHalfPlane K (t : Real.Angle)).2) (hr : 0 < r) :
    p - r • normalVector (((a + b) / 2 : ℝ) : Real.Angle) ∉
      Set.range (brokenSupportPath K a b) ∪ A.val.carrier := by
  intro hq
  rcases hq with hq | hq
  · rcases brokenSupportPath_mem_support_eq K hab hba hq with hqa | hqb
    · exact (ne_of_lt (sub_pos_midpoint_normal_inner_lt_support K hab hba hp hr a
        ⟨le_rfl, hab.le⟩)) hqa
    · exact (ne_of_lt (sub_pos_midpoint_normal_inner_lt_support K hab hba hp hr b
        ⟨hab.le, le_rfl⟩)) hqb
  · obtain ⟨t, ht, hqt⟩ := convexBoundaryArc_exists_support_eq K hab.le (hA.1 ▸ hq)
    exact (ne_of_lt (sub_pos_midpoint_normal_inner_lt_support K hab hba hp hr t ht)) hqt

private theorem boundaryLoop_component_unbounded_of_mem_supportIntersection
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (A : RectifiableOrientedArc) (hA : RealizesConvexArc K a b A) {p : Point}
    (hpX : p ∈ ⋂ t ∈ Set.Icc a b,
      (supportingLineHalfPlane K (t : Real.Angle)).2)
    (hpΓ : p ∉ Set.range (brokenSupportPath K a b) ∪ A.val.carrier) :
    ¬ Bornology.IsBounded (connectedComponentIn
      (Set.range (brokenSupportPath K a b) ∪ A.val.carrier)ᶜ p) := by
  let n := normalVector (((a + b) / 2 : ℝ) : Real.Angle)
  let f : ℝ → Point := fun r ↦ p - r • n
  have hf : Continuous f := continuous_const.sub (continuous_id.smul continuous_const)
  have hpre : IsPreconnected (f '' Set.Ici 0) :=
    isPreconnected_Ici.image f hf.continuousOn
  have hsub : f '' Set.Ici 0 ⊆
      (Set.range (brokenSupportPath K a b) ∪ A.val.carrier)ᶜ := by
    rintro q ⟨r, hr, rfl⟩
    by_cases hr0 : r = 0
    · simpa [f, hr0] using hpΓ
    · exact sub_pos_midpoint_normal_not_mem_boundary_loop K hab hba A hA hpX
        (lt_of_le_of_ne hr (Ne.symm hr0))
  have hpmem : p ∈ f '' Set.Ici 0 := ⟨0, by simp, by simp [f]⟩
  have hcomp := hpre.subset_connectedComponentIn hpmem hsub
  intro hb
  obtain ⟨C, hC⟩ := hb.exists_norm_le
  have hn : ‖n‖ = 1 := norm_normalVector_real ((a + b) / 2)
  let r := max 0 (C + ‖p‖ + 1)
  have hr : 0 ≤ r := le_max_left _ _
  have hq := hC (f r) (hcomp ⟨r, hr, rfl⟩)
  have hdiff : ‖r • n‖ ≤ C + ‖p‖ := by
    calc
      ‖r • n‖ = ‖p - f r‖ := by simp [f]
      _ ≤ ‖p‖ + ‖f r‖ := norm_sub_le _ _
      _ ≤ C + ‖p‖ := by linarith
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, hn, mul_one] at hdiff
  have hlower : C + ‖p‖ + 1 ≤ r := le_max_right _ _
  linarith

private theorem jordanInterior_boundaryLoop_disjoint_supportIntersection
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (A : RectifiableOrientedArc) (hA : RealizesConvexArc K a b A) :
    Disjoint (jordanInterior (Set.range (brokenSupportPath K a b) ∪ A.val.carrier))
      (⋂ t ∈ Set.Icc a b, (supportingLineHalfPlane K (t : Real.Angle)).2) := by
  rw [Set.disjoint_left]
  intro p hpI hpX
  exact boundaryLoop_component_unbounded_of_mem_supportIntersection
    K hab hba A hA hpX hpI.1 hpI.2

private theorem isClosed_supportingLineHalfPlane_lower
    (K : ConvexBody Point) (t : Real.Angle) :
    IsClosed (supportingLineHalfPlane K t).2 := by
  exact isClosed_le (continuous_id.inner continuous_const) continuous_const

private theorem convex_supportingLineHalfPlane_lower
    (K : ConvexBody Point) (t : Real.Angle) :
    Convex ℝ (supportingLineHalfPlane K t).2 := by
  intro x hx y hy u v hu hv huv
  change inner ℝ x (normalVector t) ≤ supportValue K t at hx
  change inner ℝ y (normalVector t) ≤ supportValue K t at hy
  change inner ℝ (u • x + v • y) (normalVector t) ≤ supportValue K t
  rw [inner_add_left, inner_smul_left, inner_smul_left]
  simp only [RCLike.conj_to_real]
  calc
    u * inner ℝ x (normalVector t) + v * inner ℝ y (normalVector t) ≤
        u * supportValue K t + v * supportValue K t :=
      add_le_add (mul_le_mul_of_nonneg_left hx hu) (mul_le_mul_of_nonneg_left hy hv)
    _ = supportValue K t := by rw [← add_mul, huv, one_mul]

private theorem jordanInterior_boundaryLoop_subset_endpointHalfPlanes
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (hne : (edgeVertices K (a : Real.Angle)).1 ≠
      (edgeVertices K (b : Real.Angle)).2)
    (A : RectifiableOrientedArc) (p : ArcBVParametrization A.val)
    (hA : RealizesConvexArc K a b A) :
    jordanInterior (Set.range (brokenSupportPath K a b) ∪ A.val.carrier) ⊆
      interior ((supportingLineHalfPlane K a).2 ∩
        (supportingLineHalfPlane K b).2) := by
  apply jordanInterior_subset_interior_of_subset_closed_convex
    (convexArc_broken_isJordanCurve K hab hba hne A p hA)
  · exact (Set.range_nonempty _).inl
  · exact brokenSupportPath_union_convexArc_subset_endpointHalfPlanes K hab hba A hA
  · exact (convex_supportingLineHalfPlane_lower K a).inter
      (convex_supportingLineHalfPlane_lower K b)
  · exact (isClosed_supportingLineHalfPlane_lower K a).inter
      (isClosed_supportingLineHalfPlane_lower K b)

private theorem concatThree_first_image_jordan
    (p₀ p₁ p₂ : ContinuousBVPaths 0 1)
    (h01 : p₀.val ⟨1, by norm_num⟩ = p₁.val ⟨0, by norm_num⟩)
    (h12 : p₁.val ⟨1, by norm_num⟩ = p₂.val ⟨0, by norm_num⟩) :
    (concatThreeUnitPaths_jordan p₀ p₁ p₂ h01 h12).val ''
        Set.Icc (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 2) ⟨1 / 2, by norm_num⟩ =
      Set.range p₀.val := by
  apply Set.Subset.antisymm
  · rintro z ⟨t, ht, rfl⟩
    have htt : (t : ℝ) ≤ 1 / 2 := by exact_mod_cast ht.2
    let u : Set.Icc (0 : ℝ) 1 := ⟨2 * (t : ℝ), by
      constructor <;> nlinarith [t.property.1, htt]⟩
    refine ⟨u, ?_⟩
    have heq : (⟨(u : ℝ) / 2, by
        constructor <;> nlinarith [u.property.1, u.property.2]⟩ : Set.Icc (0 : ℝ) 2) = t := by
      apply Subtype.ext
      dsimp [u]
      ring
    rw [← heq]
    exact (concatThreeUnitPaths_first_jordan p₀ p₁ p₂ h01 h12 u).symm
  · rintro z ⟨u, rfl⟩
    let t : Set.Icc (0 : ℝ) 2 := ⟨(u : ℝ) / 2, by
      constructor <;> nlinarith [u.property.1, u.property.2]⟩
    refine ⟨t, ⟨by exact Subtype.coe_le_coe.mp t.property.1,
      by change (t : ℝ) ≤ 1 / 2; dsimp [t]; linarith [u.property.2]⟩, ?_⟩
    exact concatThreeUnitPaths_first_jordan p₀ p₁ p₂ h01 h12 u

private theorem concatThree_convexArc_oriented
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (hne : (edgeVertices K (a : Real.Angle)).1 ≠
      (edgeVertices K (b : Real.Angle)).2)
    (A : RectifiableOrientedArc) (p : ArcBVParametrization A.val)
    (hA : RealizesConvexArc K a b A)
    (p₂ : ContinuousBVPaths 0 1)
    (hp₂ : p₂.val = (reverseArcPath p).val ∘ unitParam_jordan p.a p.b p.ordered)
    (h01 : (lineSegmentBVPath (edgeVertices K a).1 (supportingIntersection K a b)).val
      ⟨1, by norm_num⟩ =
      (lineSegmentBVPath (supportingIntersection K a b) (edgeVertices K b).2).val
        ⟨0, by norm_num⟩)
    (h12 : (lineSegmentBVPath (supportingIntersection K a b) (edgeVertices K b).2).val
      ⟨1, by norm_num⟩ = p₂.val ⟨0, by norm_num⟩) :
    IsOrientedJordanParametrization (by norm_num : (0 : ℝ) ≤ 2)
      (Set.range (concatThreeUnitPaths_jordan
        (lineSegmentBVPath (edgeVertices K a).1 (supportingIntersection K a b))
        (lineSegmentBVPath (supportingIntersection K a b) (edgeVertices K b).2)
        p₂ h01 h12).val) true
      (concatThreeUnitPaths_jordan
        (lineSegmentBVPath (edgeVertices K a).1 (supportingIntersection K a b))
        (lineSegmentBVPath (supportingIntersection K a b) (edgeVertices K b).2)
        p₂ h01 h12).val := by
  let p₀ := lineSegmentBVPath (edgeVertices K a).1 (supportingIntersection K a b)
  let p₁ := lineSegmentBVPath (supportingIntersection K a b) (edgeVertices K b).2
  let q := concatUnitPaths_jordan p₀ p₁ h01
  let q' := reparamTwoToUnit_jordan q
  let γ := concatThreeUnitPaths_jordan p₀ p₁ p₂ h01 h12
  have hq' : q'.val = brokenSupportPath K a b :=
    reparam_support_segments_eq_brokenSupportPath K a b h01
  have hpq : Function.Injective q'.val := hq' ▸ brokenSupportPath_injective K hab hba hne
  have hPneQ : A.val.startPoint ≠ A.val.endPoint := by simpa [hA.2.1, hA.2.2] using hne
  have hp₂inj := reverseArcUnitPath_injective p p₂ hp₂ hPneQ
  have hqrange : Set.range q'.val = Set.range (brokenSupportPath K a b) := by rw [hq']
  have hp₂range : Set.range p₂.val = A.val.carrier := range_reverseArcUnitPath p p₂ hp₂
  have hmeet : Set.range q'.val ∩ Set.range p₂.val =
      {q'.val ⟨0, by norm_num⟩, q'.val ⟨1, by norm_num⟩} := by
    rw [hqrange, hp₂range, hA.1,
      brokenSupportPath_range_inter_convexBoundaryArc K hab hba hne, hq']
    simp [brokenSupportPath]
  have hclose : p₂.val ⟨1, by norm_num⟩ = q'.val ⟨0, by norm_num⟩ := by
    rw [hp₂]
    simp [q', hq', brokenSupportPath, reverseArcPath, unitParam_jordan, Set.Icc.reverse,
      hA.2.1, p.start_eq]
  have hjoin : q'.val ⟨1, by norm_num⟩ = p₂.val ⟨0, by norm_num⟩ := by
    rw [show q'.val ⟨1, by norm_num⟩ = q.val ⟨2, by norm_num⟩ from
      reparamTwoToUnit_one q]
    exact (concatUnitPaths_jordan_end p₀ p₁ h01).trans h12
  have hinj := injOn_concatUnitPaths_jordan q' p₂ hjoin
    hclose hpq hp₂inj hmeet
  have hrange : Set.range γ.val = Set.range (brokenSupportPath K a b) ∪ A.val.carrier := by
    rw [show γ = concatThreeUnitPaths_jordan p₀ p₁ p₂ h01 h12 by rfl]
    rw [range_concatThreeUnitPaths_jordan, hp₂range]
    have hq'q : Set.range q'.val = Set.range q.val :=
      range_comp_surjective q.val doubleParam_jordan surjective_doubleParam_jordan
    rw [← Function.range_concatUnitIntervals p₀.val p₁.val h01]
    change Set.range q.val ∪ A.val.carrier = _
    rw [← hq'q, hqrange]
  have hJordan := convexArc_broken_isJordanCurve K hab hba hne A p hA
  obtain ⟨d, hd, hdir⟩ := supportingIntersection_eq_fst_add_pos_tangent K hab hba hne
  have hclosedγ : γ.val ⟨0, by norm_num⟩ = γ.val ⟨2, by norm_num⟩ := by
    simpa [γ, concatThreeUnitPaths_jordan, concatUnitPaths_jordan, q', q] using hclose.symm
  have hinjγ : Set.InjOn γ.val {t | (t : ℝ) < 2} := by
    simpa [γ, concatThreeUnitPaths_jordan, q', q] using hinj
  have hhalfγ (t : Set.Icc (0 : ℝ) 2) :
      γ.val t ∈ normalHalfPlane (a : Real.Angle) (supportValue K a) false false :=
    (brokenSupportPath_union_convexArc_subset_endpointHalfPlanes K hab hba A hA
      (hrange ▸ Set.mem_range_self t)).1
  let s : Set.Icc (0 : ℝ) 2 := ⟨0, by norm_num⟩
  let t : Set.Icc (0 : ℝ) 2 := ⟨1 / 2, by norm_num⟩
  have hs : γ.val s = (edgeVertices K (a : Real.Angle)).1 := by
    simpa [s, γ, p₀, lineSegmentBVPath] using
      concatThreeUnitPaths_first_jordan p₀ p₁ p₂ h01 h12 ⟨0, by norm_num⟩
  have ht : γ.val t = supportingIntersection K a b := by
    simpa [t, γ, p₀, lineSegmentBVPath] using
      concatThreeUnitPaths_first_jordan p₀ p₁ p₂ h01 h12 ⟨1, by norm_num⟩
  exact jordan_counterclockwise_of_supporting_segment 0 2 (by norm_num) γ.val
    γ.property.1 (hrange ▸ hJordan) hclosedγ hinjγ
    (a : Real.Angle) (supportValue K a) hhalfγ s t (by
      change (0 : ℝ) < 1 / 2
      norm_num)
    (by rw [hs]; exact (edgeVertices_fst_mem K (a : Real.Angle)).2)
    d hd (by rw [hs, ht]; exact hdir)
    (by
      rw [hs, ht]
      rw [show γ.val '' Set.Icc s t = Set.range p₀.val by
        simpa [s, t, γ] using concatThree_first_image_jordan p₀ p₁ p₂ h01 h12]
      exact Path.range_segment _ _)

private theorem exists_rectifiableOrientedArc_segment_jordan (P Q : Point) (hPQ : P ≠ Q) :
    ∃ A : RectifiableOrientedArc,
      A.val.carrier = segment ℝ P Q ∧ A.val.startPoint = P ∧ A.val.endPoint = Q := by
  let Γ : OrientedJordanArc :=
    { carrier := segment ℝ P Q
      startPoint := P
      endPoint := Q
      parametrizable := by
        refine ⟨0, 1, by norm_num, Path.segment P Q,
          (Path.segment P Q).continuous, Path.segment_injective_of_ne hPQ,
          Path.range_segment P Q, ?_, ?_⟩ <;> simp }
  let z : ArcBVParametrization Γ :=
    { a := 0
      b := 1
      ordered := by norm_num
      path := lineSegmentBVPath P Q
      injective := Path.segment_injective_of_ne hPQ
      range_eq := Path.range_segment P Q
      start_eq := by simp [lineSegmentBVPath, Γ]
      end_eq := by simp [lineSegmentBVPath, Γ] }
  let A : RectifiableOrientedArc := ⟨Γ, ⟨z⟩⟩
  exact ⟨A, rfl, rfl, rfl⟩

private theorem exists_rectifiableOrientedArc_convexBoundaryArc_jordan
    (K : ConvexBody Point) (a b : ℝ) (hab : a < b) (hba : b < a + Real.pi)
    (hne : (edgeVertices K a).1 ≠ (edgeVertices K b).2) :
    ∃ A : RectifiableOrientedArc, RealizesConvexArc K a b A := by
  let P := (edgeVertices K (a : Real.Angle)).1
  let Q := (edgeVertices K (b : Real.Angle)).2
  let O := supportingIntersection K a b
  obtain ⟨-, hcut⟩ := convexBoundaryArc_cut K a b hab hba P Q O rfl rfl rfl
  obtain ⟨hncol, t, c, K', hat, htb, hPt, hQt, hcO, hK', hleft, hmiddle,
      hright, hterminal⟩ := hcut hne
  by_cases hInt : (interior (K' : Set Point)).Nonempty
  · obtain ⟨A, hcarrier, hstart, hend⟩ :=
      exists_rectifiableOrientedArc_convexBoundaryArc_of_cut K K' a b t c P Q
        hat htb hba hne hPt hQt rfl rfl hleft hmiddle hright hterminal hInt
    exact ⟨A, hcarrier, hstart, hend⟩
  · have hInt' : interior (K' : Set Point) = ∅ := Set.not_nonempty_iff_eq_empty.mp hInt
    have harc := convexBoundaryArc_eq_segment_of_cut_interior_empty K K' a b t c P Q
      hat htb hba hne hPt hQt rfl rfl hleft hmiddle hright hInt'
    obtain ⟨A, hcarrier, hstart, hend⟩ :=
      exists_rectifiableOrientedArc_segment_jordan P Q hne
    exact ⟨A, hcarrier.trans harc.symm, hstart, hend⟩

/-- The supporting segments and reversed convex boundary arc form a counterclockwise Jordan
curve. -/
theorem convexBoundaryArc_jordan (K : ConvexBody Point) (a b : ℝ)
    (hab : a < b) (hba : b < a + Real.pi)
    (hne : (edgeVertices K a).1 ≠ (edgeVertices K b).2) :
    ∃ (A : RectifiableOrientedArc) (p : ArcBVParametrization A.val)
      (γ : RectifiablePathData) (pieces : Fin 3 → RectifiablePathData),
      RealizesConvexArc K a b A ∧
      IsSegmentTraversal (pieces 0) (edgeVertices K a).1 (supportingIntersection K a b) ∧
      IsSegmentTraversal (pieces 1) (supportingIntersection K a b) (edgeVertices K b).2 ∧
      IsReverseArcTraversal (pieces 2) p ∧ IsPathConcatenation γ pieces ∧
      IsOrientedJordanParametrization γ.ordered (Set.range γ.path.val) true γ.path.val ∧
      jordanInterior (Set.range γ.path.val) ⊆
        interior ((supportingLineHalfPlane K a).2 ∩ (supportingLineHalfPlane K b).2) ∧
      Disjoint (jordanInterior (Set.range γ.path.val))
        (⋂ t ∈ Set.Icc a b, (supportingLineHalfPlane K (t : Real.Angle)).2) := by
  obtain ⟨A, hA⟩ :=
    exists_rectifiableOrientedArc_convexBoundaryArc_jordan K a b hab hba hne
  let p : ArcBVParametrization A.val := Classical.choice A.property
  let P := (edgeVertices K (a : Real.Angle)).1
  let Q := (edgeVertices K (b : Real.Angle)).2
  let O := supportingIntersection K a b
  let p₀ := lineSegmentBVPath P O
  let p₁ := lineSegmentBVPath O Q
  obtain ⟨p₂, hp₂, hp₂rev⟩ := exists_reverseArcUnitPath p
  have h01 : p₀.val ⟨1, by norm_num⟩ = p₁.val ⟨0, by norm_num⟩ := by
    simp [p₀, p₁, lineSegmentBVPath]
  have h12 : p₁.val ⟨1, by norm_num⟩ = p₂.val ⟨0, by norm_num⟩ := by
    rw [hp₂]
    change p₁.val ⟨1, by norm_num⟩ =
      (reverseArcPath p).val (unitParam_jordan p.a p.b p.ordered ⟨0, by norm_num⟩)
    rw [show unitParam_jordan p.a p.b p.ordered ⟨0, by norm_num⟩ =
      ⟨p.a, le_rfl, p.ordered⟩ by exact Set.Icc.convexComb_zero _ _]
    rw [reverseArcPath_start]
    simpa [p₁, Q, lineSegmentBVPath, Path.segment_apply,
      AffineMap.lineMap_apply_module'] using hA.2.2.symm
  let γpath := concatThreeUnitPaths_jordan p₀ p₁ p₂ h01 h12
  let γ : RectifiablePathData :=
    { a := 0, b := 2, ordered := by norm_num, path := γpath }
  let pieces : Fin 3 → RectifiablePathData :=
    ![{ a := 0, b := 1, ordered := by norm_num, path := p₀ },
      { a := 0, b := 1, ordered := by norm_num, path := p₁ },
      { a := 0, b := 1, ordered := by norm_num, path := p₂ }]
  have horient := concatThree_convexArc_oriented K hab hba hne A p hA p₂ hp₂ h01 h12
  have hrange : Set.range γ.path.val =
      Set.range (brokenSupportPath K a b) ∪ A.val.carrier := by
    change Set.range (concatThreeUnitPaths_jordan p₀ p₁ p₂ h01 h12).val = _
    rw [range_concatThreeUnitPaths_jordan, range_reverseArcUnitPath p p₂ hp₂]
    rw [← Function.range_concatUnitIntervals p₀.val p₁.val h01]
    let q := concatUnitPaths_jordan p₀ p₁ h01
    have hrepr : Set.range (reparamTwoToUnit_jordan q).val = Set.range q.val :=
      range_comp_surjective q.val doubleParam_jordan surjective_doubleParam_jordan
    change Set.range q.val ∪ A.val.carrier = _
    rw [← hrepr, show (reparamTwoToUnit_jordan q).val = brokenSupportPath K a b by
      simpa [q, p₀, p₁, P, Q, O] using
        reparam_support_segments_eq_brokenSupportPath K a b h01]
  refine ⟨A, p, γ, pieces, hA, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [pieces, P, O, Matrix.cons_val_zero] using
      isSegmentTraversal_lineSegmentBVPath P O
  · simpa [pieces, Q, O, Matrix.cons_val_zero, Matrix.cons_val_one] using
      isSegmentTraversal_lineSegmentBVPath O Q
  · simpa [pieces, Matrix.cons_val_zero, Matrix.cons_val_one] using hp₂rev
  · simpa [γ, γpath, pieces] using
      isPathConcatenation_concatThreeUnitPaths_jordan p₀ p₁ p₂ h01 h12
  · simpa [γ, γpath, p₀, p₁] using horient
  · rw [hrange]
    exact jordanInterior_boundaryLoop_subset_endpointHalfPlanes K hab hba hne A p hA
  · rw [hrange]
    exact jordanInterior_boundaryLoop_disjoint_supportIntersection K hab hba A hA
