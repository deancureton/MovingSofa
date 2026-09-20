import MovingSofa.Curve.AreaAdditivity
import MovingSofa.Curve.AreaTransport
import MovingSofa.ForMathlib.Topology.Order.Concatenation

noncomputable section

namespace MovingSofa

open MeasureTheory Set

/-- Restrict a continuous BV path to a closed subinterval. -/
def ContinuousBVPaths.restrict {a b : ℝ} (x : ContinuousBVPaths a b)
    (l u : Set.Icc a b) (_hlu : l ≤ u) : ContinuousBVPaths (l : ℝ) u :=
  let ι : Set.Icc (l : ℝ) u → Set.Icc a b := fun t ↦
    ⟨t, le_trans l.property.1 t.property.1, le_trans t.property.2 u.property.2⟩
  ⟨x.val ∘ ι, x.property.1.comp (continuous_subtype_val.subtype_mk _), fun i ↦
    ne_top_of_le_ne_top (x.property.2 i)
      (eVariationOn.comp_le_of_monotoneOn (fun t ↦ x.val t i) ι
        (fun _ _ _ _ h ↦ h) (mapsTo_univ ι _))⟩

private theorem curveArea_restrict_Ioc
    {a b : ℝ} (x : ContinuousBVPaths a b) (l u : Set.Icc a b) (hlu : l ≤ u) :
    (intervalStieltjesIntegral (continuousBVCoordinate x 1)
        (fun t ↦ x.val t 0) (Ioc l u) -
      intervalStieltjesIntegral (continuousBVCoordinate x 0)
        (fun t ↦ x.val t 1) (Ioc l u)) / 2 =
      curveAreaFunctional (ContinuousBVPaths.restrict x l u hlu) := by
  unfold curveAreaFunctional
  rw [intervalStieltjesIntegral_Ioc_eq_inclusion
      (continuousBVCoordinate x 1)
      ((PiLp.continuous_apply 2 _ 1).comp x.property.1)
      (fun t ↦ x.val t 0) ((PiLp.continuous_apply 2 _ 0).comp x.property.1)
      l u hlu,
    intervalStieltjesIntegral_Ioc_eq_inclusion
      (continuousBVCoordinate x 0)
      ((PiLp.continuous_apply 2 _ 0).comp x.property.1)
      (fun t ↦ x.val t 1) ((PiLp.continuous_apply 2 _ 1).comp x.property.1)
      l u hlu]
  rfl

/-- Signed path area is additive along any monotone chain of cuts of the parameter interval. -/
theorem curveArea_eq_sum_restrict {a b : ℝ} (x : ContinuousBVPaths a b)
    {n : ℕ} (cuts : Fin (n + 1) → Set.Icc a b) (hcuts : Monotone cuts)
    (hzero : (cuts 0 : ℝ) = a) (hlast : (cuts (Fin.last n) : ℝ) = b) :
    curveAreaFunctional x =
      ∑ i : Fin n, curveAreaFunctional (ContinuousBVPaths.restrict x (cuts i.castSucc)
        (cuts i.succ) (hcuts (Fin.castSucc_le_succ i))) := by
  simp_rw [← curveArea_restrict_Ioc x]
  unfold curveAreaFunctional
  rw [intervalStieltjesIntegral_eq_sum_Ioc (continuousBVCoordinate x 1)
      ((PiLp.continuous_apply 2 _ 1).comp x.property.1)
      (fun t ↦ x.val t 0) ((PiLp.continuous_apply 2 _ 0).comp x.property.1)
      cuts hcuts hzero hlast,
    intervalStieltjesIntegral_eq_sum_Ioc (continuousBVCoordinate x 0)
      ((PiLp.continuous_apply 2 _ 0).comp x.property.1)
      (fun t ↦ x.val t 1) ((PiLp.continuous_apply 2 _ 1).comp x.property.1)
      cuts hcuts hzero hlast, ← Finset.sum_sub_distrib]
  simp_rw [div_eq_mul_inv, Finset.sum_mul]

/-- Split the signed area of a continuous BV path at any parameter value. -/
theorem curveArea_eq_restriction_add_restriction
    {a b : ℝ} (hab : a ≤ b) (x : ContinuousBVPaths a b) (s : Set.Icc a b) :
    let a' : Set.Icc a b := ⟨a, le_rfl, hab⟩
    let b' : Set.Icc a b := ⟨b, hab, le_rfl⟩
    curveAreaFunctional x =
      curveAreaFunctional (ContinuousBVPaths.restrict x a' s s.property.1) +
      curveAreaFunctional (ContinuousBVPaths.restrict x s b' s.property.2) := by
  let a' : Set.Icc a b := ⟨a, le_rfl, hab⟩
  let b' : Set.Icc a b := ⟨b, hab, le_rfl⟩
  have hs1 : a ≤ (s : ℝ) := s.property.1
  have hs2 : (s : ℝ) ≤ b := s.property.2
  change curveAreaFunctional x =
    curveAreaFunctional (ContinuousBVPaths.restrict x a' s hs1) +
      curveAreaFunctional (ContinuousBVPaths.restrict x s b' hs2)
  have hcuts : Monotone (![a', s, b'] : Fin 3 → Set.Icc a b) := by
    refine Fin.monotone_iff_le_succ.mpr fun i ↦ ?_
    fin_cases i
    · exact hs1
    · exact hs2
  have hsum := curveArea_eq_sum_restrict x ![a', s, b'] hcuts rfl rfl
  rw [Fin.sum_univ_two] at hsum
  exact hsum

/-- The tail and head restrictions have signed areas summing to the original area. -/
theorem curveArea_cyclic_cut_sum
    {a b : ℝ} (hab : a ≤ b) (x : ContinuousBVPaths a b) (s : Set.Icc a b) :
    let a' : Set.Icc a b := ⟨a, le_rfl, hab⟩
    let b' : Set.Icc a b := ⟨b, hab, le_rfl⟩
    curveAreaFunctional x =
      curveAreaFunctional (ContinuousBVPaths.restrict x s b' s.property.2) +
      curveAreaFunctional (ContinuousBVPaths.restrict x a' s s.property.1) := by
  rw [curveArea_eq_restriction_add_restriction hab x s, add_comm]

/-- Package a restricted continuous BV path with its interval endpoints. -/
def ContinuousBVPaths.restrictionData {a b : ℝ} (x : ContinuousBVPaths a b)
    (l u : Set.Icc a b) (hlu : l ≤ u) : RectifiablePathData where
  a := l
  b := u
  ordered := hlu
  path := ContinuousBVPaths.restrict x l u hlu

/-- A tail-then-head concatenation preserves the signed area. -/
theorem curveArea_cyclic_rotation
    {a b c d : ℝ} (hab : a ≤ b) (x : ContinuousBVPaths a b)
    (s : Set.Icc a b) (rotated : ContinuousBVPaths c d) (hcd : c ≤ d)
    (hrot : IsPathConcatenation
      { a := c, b := d, ordered := hcd, path := rotated }
      ![ContinuousBVPaths.restrictionData x s ⟨b, hab, le_rfl⟩ s.property.2,
        ContinuousBVPaths.restrictionData x ⟨a, le_rfl, hab⟩ s s.property.1]) :
    curveAreaFunctional rotated = curveAreaFunctional x := by
  rw [curveArea_concatenation _ _ hrot]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    ContinuousBVPaths.restrictionData]
  exact (curveArea_cyclic_cut_sum hab x s).symm

private theorem boundedVariation_concatUnitIntervals_coordinate
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
    change ((0 : ℝ) ≤ t ∧ (t : ℝ) ≤ 2) ↔ True
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
            p.val (Set.projIcc 0 1 (by norm_num) (t : ℝ)) i)
            (Set.Icc z o) := by
              apply eVariationOn.congr
              intro t ht
              have ht' : (t : ℝ) ≤ 1 := by exact ht.2
              simp [f, Function.concatUnitIntervals, ht']
      _ ≤ eVariationOn (fun t ↦ p.val t i) Set.univ :=
        by
          simpa only [Function.comp_def] using
            (eVariationOn.comp_le_of_monotoneOn (fun t ↦ p.val t i)
              (t := Set.Icc z o)
              (fun t : Set.Icc (0 : ℝ) 2 ↦ Set.projIcc 0 1 (by norm_num) (t : ℝ))
              (fun _ _ _ _ hxy ↦ Set.monotone_projIcc (by norm_num) hxy)
              (mapsTo_univ _ _))
  · refine ne_top_of_le_ne_top (q.property.2 i) ?_
    calc
      eVariationOn f (Set.Icc o w) =
          eVariationOn
            (fun t : Set.Icc (0 : ℝ) 2 ↦
              q.val (Set.projIcc 0 1 (by norm_num) ((t : ℝ) - 1)) i)
            (Set.Icc o w) := by
              apply eVariationOn.congr
              intro t ht
              have hleft : (1 : ℝ) ≤ t := by exact ht.1
              have ht' : ¬(t : ℝ) ≤ 1 ∨ (t : ℝ) = 1 := by
                rcases lt_or_eq_of_le hleft with h | h
                · exact Or.inl (not_le_of_gt h)
                · exact Or.inr h.symm
              rcases ht' with ht' | htEq
              · simp [f, Function.concatUnitIntervals, ht']
              · simpa [f, Function.concatUnitIntervals, htEq] using congrArg (fun z ↦ z i) hjoin
      _ ≤ eVariationOn (fun t ↦ q.val t i) Set.univ :=
        by
          simpa only [Function.comp_def] using
            (eVariationOn.comp_le_of_monotoneOn (fun t ↦ q.val t i)
              (t := Set.Icc o w)
              (fun t : Set.Icc (0 : ℝ) 2 ↦
                Set.projIcc 0 1 (by norm_num) ((t : ℝ) - 1))
              (fun _ _ _ _ hxy ↦ Set.monotone_projIcc (by norm_num)
                (sub_le_sub_right (show (_ : ℝ) ≤ _ from hxy) 1))
              (mapsTo_univ _ _))

private def concatUnitPaths (p q : ContinuousBVPaths 0 1)
    (hjoin : p.val ⟨1, by norm_num⟩ = q.val ⟨0, by norm_num⟩) :
    ContinuousBVPaths 0 2 :=
  ⟨Function.concatUnitIntervals p.val q.val,
    Function.continuous_concatUnitIntervals p.property.1 q.property.1 hjoin,
    boundedVariation_concatUnitIntervals_coordinate p q hjoin⟩

private theorem isPathConcatenation_concatUnitPaths
    (p q : ContinuousBVPaths 0 1)
    (hjoin : p.val ⟨1, by norm_num⟩ = q.val ⟨0, by norm_num⟩) :
    IsPathConcatenation
      { a := 0, b := 2, ordered := by norm_num, path := concatUnitPaths p q hjoin }
      ![{ a := 0, b := 1, ordered := by norm_num, path := p },
        { a := 0, b := 1, ordered := by norm_num, path := q }] := by
  let cuts : Fin 3 → Set.Icc (0 : ℝ) 2 :=
    ![⟨0, by norm_num⟩, ⟨1, by norm_num⟩, ⟨2, by norm_num⟩]
  refine ⟨by norm_num, cuts, ?_, rfl, rfl, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [cuts, Matrix.cons_val_zero,
      Matrix.cons_val_one] at hij ⊢
  intro i
  fin_cases i
  · let φ : Set.Icc (0 : ℝ) 1 → Set.Icc (cuts (Fin.castSucc 0) : ℝ)
        (cuts (Fin.succ 0) : ℝ) := fun t ↦ ⟨t, by simp [cuts]⟩
    let ψ : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1 := id
    refine ⟨φ, ψ, ?_, ?_, ?_, continuous_id, monotone_id, Function.surjective_id, ?_⟩
    · exact Continuous.subtype_mk continuous_subtype_val _
    · intro x y hxy
      exact hxy
    · intro y
      exact ⟨⟨y, by simpa [cuts] using y.property⟩, Subtype.ext rfl⟩
    · intro t
      have ht : (t : ℝ) ≤ 1 := t.property.2
      simp [φ, ψ, concatUnitPaths, Function.concatUnitIntervals, ht]
  · let φ : Set.Icc (0 : ℝ) 1 → Set.Icc (cuts (Fin.castSucc 1) : ℝ)
        (cuts (Fin.succ 1) : ℝ) := fun t ↦ ⟨(t : ℝ) + 1, by
          change (1 : ℝ) ≤ (t : ℝ) + 1 ∧ (t : ℝ) + 1 ≤ 2
          constructor <;> linarith [t.property.1, t.property.2]⟩
    let ψ : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1 := id
    refine ⟨φ, ψ, ?_, ?_, ?_, continuous_id, monotone_id, Function.surjective_id, ?_⟩
    · exact Continuous.subtype_mk (continuous_subtype_val.add continuous_const) _
    · intro x y hxy
      change (x : ℝ) + 1 ≤ (y : ℝ) + 1
      linarith [show (x : ℝ) ≤ y from hxy]
    · intro y
      refine ⟨⟨(y : ℝ) - 1, ?_⟩, Subtype.ext ?_⟩
      · have hy1 : (1 : ℝ) ≤ y := by exact y.property.1
        have hy2 : (y : ℝ) ≤ 2 := by exact y.property.2
        constructor <;> linarith [y.property.1, y.property.2]
      · simp [φ]
    · intro t
      by_cases ht : (t : ℝ) = 0
      · have htSub : t = (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1) := Subtype.ext ht
        rw [htSub]
        simpa [φ, ψ, concatUnitPaths, Function.concatUnitIntervals] using hjoin
      · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
        simp [φ, ψ, concatUnitPaths, Function.concatUnitIntervals, htpos]

private def unitIntervalParam (a b : ℝ) (hab : a ≤ b) :
    Set.Icc (0 : ℝ) 1 → Set.Icc a b :=
  Set.Icc.convexComb ⟨a, le_rfl, hab⟩ ⟨b, hab, le_rfl⟩

private theorem continuous_unitIntervalParam (a b : ℝ) (hab : a ≤ b) :
    Continuous (unitIntervalParam a b hab) := Set.Icc.continuous_convexComb _ _

private theorem monotone_unitIntervalParam (a b : ℝ) (hab : a ≤ b) :
    Monotone (unitIntervalParam a b hab) := by
  intro s t hst
  change (1 - (s : ℝ)) * a + (s : ℝ) * b ≤ (1 - (t : ℝ)) * a + (t : ℝ) * b
  have hst' : (s : ℝ) ≤ t := hst
  nlinarith

private theorem surjective_unitIntervalParam (a b : ℝ) (hab : a ≤ b) :
    Function.Surjective (unitIntervalParam a b hab) := by
  intro x
  rcases hab.eq_or_lt with rfl | hab
  · refine ⟨⟨0, by norm_num⟩, Subtype.ext ?_⟩
    change (1 - (0 : ℝ)) * a + 0 * a = (x : ℝ)
    have hx : (x : ℝ) = a := le_antisymm x.property.2 x.property.1
    simp [hx]
  · refine ⟨⟨((x : ℝ) - a) / (b - a), ?_⟩, Subtype.ext ?_⟩
    · constructor
      · exact div_nonneg (sub_nonneg.mpr x.property.1) (sub_nonneg.mpr hab.le)
      · exact (div_le_one (sub_pos.mpr hab)).2 (sub_le_sub_right x.property.2 a)
    · change (1 - ((x : ℝ) - a) / (b - a)) * a + ((x : ℝ) - a) / (b - a) * b = (x : ℝ)
      field_simp [ne_of_gt (sub_pos.mpr hab)]
      ring

private theorem unitIntervalParam_zero (a b : ℝ) (hab : a ≤ b) :
    unitIntervalParam a b hab ⟨0, by norm_num⟩ = ⟨a, le_rfl, hab⟩ := by
  exact Set.Icc.convexComb_zero _ _

private theorem unitIntervalParam_one (a b : ℝ) (hab : a ≤ b) :
    unitIntervalParam a b hab ⟨1, by norm_num⟩ = ⟨b, hab, le_rfl⟩ := by
  exact Set.Icc.convexComb_one _ _

/-- Rotate a closed continuous BV path by concatenating its tail and head. -/
theorem exists_cyclic_rotation_path {a b : ℝ} (hab : a ≤ b) (x : ContinuousBVPaths a b)
    (s : Set.Icc a b) (hx : x.val ⟨b, hab, le_rfl⟩ = x.val ⟨a, le_rfl, hab⟩) :
    ∃ rotated : ContinuousBVPaths 0 2,
      rotated.val = Function.concatUnitIntervals
        (x.val ∘ Set.Icc.convexComb s ⟨b, hab, le_rfl⟩)
        (x.val ∘ Set.Icc.convexComb ⟨a, le_rfl, hab⟩ s) ∧
      IsPathConcatenation { a := 0, b := 2, ordered := by norm_num, path := rotated }
        ![ContinuousBVPaths.restrictionData x s ⟨b, hab, le_rfl⟩ s.property.2,
          ContinuousBVPaths.restrictionData x ⟨a, le_rfl, hab⟩ s s.property.1] := by
  let tail := ContinuousBVPaths.restrict x s ⟨b, hab, le_rfl⟩ s.property.2
  let head := ContinuousBVPaths.restrict x ⟨a, le_rfl, hab⟩ s s.property.1
  obtain ⟨p, hp⟩ := continuousBVPaths_comp_monotone_surjective
    s.property.2 tail
    (unitIntervalParam s b s.property.2) (continuous_unitIntervalParam _ _ _)
    (monotone_unitIntervalParam _ _ _) (surjective_unitIntervalParam _ _ _)
  obtain ⟨q, hq⟩ := continuousBVPaths_comp_monotone_surjective
    s.property.1 head
    (unitIntervalParam a s s.property.1) (continuous_unitIntervalParam _ _ _)
    (monotone_unitIntervalParam _ _ _) (surjective_unitIntervalParam _ _ _)
  have hjoin : p.val ⟨1, by norm_num⟩ = q.val ⟨0, by norm_num⟩ := by
    rw [hp, hq]
    simp only [Function.comp_apply, unitIntervalParam_one, unitIntervalParam_zero]
    exact hx
  let rotated := concatUnitPaths p q hjoin
  have hrot : IsPathConcatenation
      { a := 0, b := 2, ordered := by norm_num, path := rotated }
      ![ContinuousBVPaths.restrictionData x s ⟨b, hab, le_rfl⟩ s.property.2,
        ContinuousBVPaths.restrictionData x ⟨a, le_rfl, hab⟩ s s.property.1] := by
    obtain ⟨hn, cuts, hm, hz, ho, hc⟩ := isPathConcatenation_concatUnitPaths p q hjoin
    refine ⟨hn, cuts, hm, hz, ho, ?_⟩
    intro i
    fin_cases i
    · obtain ⟨φ, ψ, hφc, hφm, hφs, hψc, hψm, hψs, heq⟩ := hc 0
      refine ⟨φ, unitIntervalParam s b s.property.2 ∘ ψ, hφc, hφm, hφs,
        (continuous_unitIntervalParam _ _ _).comp hψc,
        (monotone_unitIntervalParam _ _ _).comp hψm,
        (surjective_unitIntervalParam _ _ _).comp hψs, ?_⟩
      intro t
      have h := heq t
      change rotated.val _ = p.val (ψ t) at h
      rw [hp] at h
      exact h
    · obtain ⟨φ, ψ, hφc, hφm, hφs, hψc, hψm, hψs, heq⟩ := hc 1
      refine ⟨φ, unitIntervalParam a s s.property.1 ∘ ψ, hφc, hφm, hφs,
        (continuous_unitIntervalParam _ _ _).comp hψc,
        (monotone_unitIntervalParam _ _ _).comp hψm,
        (surjective_unitIntervalParam _ _ _).comp hψs, ?_⟩
      intro t
      have h := heq t
      change rotated.val _ = q.val (ψ t) at h
      rw [hq] at h
      exact h
  refine ⟨rotated, ?_, hrot⟩
  change Function.concatUnitIntervals p.val q.val = _
  rw [hp, hq]
  rfl

/-- Construct an area-preserving cyclic rotation of a closed continuous BV path. -/
theorem exists_cyclic_rotation_eq_concat {a b : ℝ} (hab : a ≤ b) (x : ContinuousBVPaths a b)
    (s : Set.Icc a b) (hx : x.val ⟨b, hab, le_rfl⟩ = x.val ⟨a, le_rfl, hab⟩) :
    ∃ rotated : ContinuousBVPaths 0 2,
      rotated.val = Function.concatUnitIntervals
        (x.val ∘ Set.Icc.convexComb s ⟨b, hab, le_rfl⟩)
        (x.val ∘ Set.Icc.convexComb ⟨a, le_rfl, hab⟩ s) ∧
      IsPathConcatenation { a := 0, b := 2, ordered := by norm_num, path := rotated }
        ![ContinuousBVPaths.restrictionData x s ⟨b, hab, le_rfl⟩ s.property.2,
          ContinuousBVPaths.restrictionData x ⟨a, le_rfl, hab⟩ s s.property.1] ∧
      curveAreaFunctional rotated = curveAreaFunctional x := by
  obtain ⟨rotated, hr, hrot⟩ := exists_cyclic_rotation_path hab x s hx
  exact ⟨rotated, hr, hrot,
    curveArea_cyclic_rotation hab x s rotated (by norm_num) hrot⟩

private theorem mem_range_convexComb {a b : ℝ} (l u z : Set.Icc a b)
    (hlz : l ≤ z) (hzu : z ≤ u) : z ∈ Set.range (Set.Icc.convexComb l u) := by
  obtain ⟨t, ht⟩ := surjective_unitIntervalParam (l : ℝ) u (hlz.trans hzu)
    ⟨z, hlz, hzu⟩
  refine ⟨t, Subtype.ext ?_⟩
  have h := congrArg (fun y : Set.Icc (l : ℝ) u ↦ (y : ℝ)) ht
  exact h

/-- Cutting and rejoining a closed path does not change its carrier. -/
theorem range_cyclic_concat {a b : ℝ} (hab : a ≤ b)
    (x : Set.Icc a b → Point) (s : Set.Icc a b)
    (hx : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩) :
    Set.range (Function.concatUnitIntervals
      (x ∘ Set.Icc.convexComb s ⟨b, hab, le_rfl⟩)
      (x ∘ Set.Icc.convexComb ⟨a, le_rfl, hab⟩ s)) = Set.range x := by
  have hjoin : (x ∘ Set.Icc.convexComb s ⟨b, hab, le_rfl⟩) ⟨1, by norm_num⟩ =
      (x ∘ Set.Icc.convexComb ⟨a, le_rfl, hab⟩ s) ⟨0, by norm_num⟩ := by
    simpa using hx.symm
  rw [Function.range_concatUnitIntervals _ _ hjoin]
  apply Set.Subset.antisymm
  · exact Set.union_subset (Set.range_comp_subset_range _ _) (Set.range_comp_subset_range _ _)
  · rintro _ ⟨t, rfl⟩
    by_cases hst : s ≤ t
    · obtain ⟨r, hr⟩ := mem_range_convexComb s ⟨b, hab, le_rfl⟩ t hst t.property.2
      exact Or.inl ⟨r, congrArg x hr⟩
    · obtain ⟨r, hr⟩ := mem_range_convexComb ⟨a, le_rfl, hab⟩ s t t.property.1
        (le_of_not_ge hst)
      exact Or.inr ⟨r, congrArg x hr⟩

/-- Every point of a nondegenerate closed path occurs before its terminal parameter. -/
theorem exists_param_lt_top_of_mem_range {a b : ℝ} (hab : a < b)
    (x : Set.Icc a b → Point)
    (hx : x ⟨a, le_rfl, hab.le⟩ = x ⟨b, hab.le, le_rfl⟩)
    {p : Point} (hp : p ∈ Set.range x) :
    ∃ s : Set.Icc a b, (s : ℝ) < b ∧ x s = p := by
  obtain ⟨s, hs⟩ := hp
  by_cases hsb : (s : ℝ) < b
  · exact ⟨s, hsb, hs⟩
  · have hst : s = ⟨b, hab.le, le_rfl⟩ :=
      Subtype.ext (le_antisymm s.property.2 (le_of_not_gt hsb))
    exact ⟨⟨a, le_rfl, hab.le⟩, hab, hx.trans (hst ▸ hs)⟩

end MovingSofa
