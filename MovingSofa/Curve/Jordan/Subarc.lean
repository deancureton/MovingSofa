import MovingSofa.Curve.Jordan.CyclicRotation
import MovingSofa.Curve.Jordan.Parametrization
import MovingSofa.Curve.Jordan.SupportingOrientation
import MovingSofa.Curve.Jordan.OrientationTransport

noncomputable section

namespace MovingSofa

open Set

/-- Reversing the parameter of a closed path preserves injectivity away from the
identified terminal endpoint. -/
theorem injOn_comp_reverse_of_closed_injOn
    {α : Type*} {a b : ℝ} (hab : a < b) (x : Set.Icc a b → α)
    (hclosed : x ⟨a, le_rfl, hab.le⟩ = x ⟨b, hab.le, le_rfl⟩)
    (hinj : Set.InjOn x {t | (t : ℝ) < b}) :
    Set.InjOn (x ∘ Set.Icc.reverse hab.le) {t | (t : ℝ) < b} := by
  intro s hs t ht hst
  change (s : ℝ) < b at hs
  change (t : ℝ) < b at ht
  have hrs_pos : a < (Set.Icc.reverse hab.le s : ℝ) := by
    change a < a + b - (s : ℝ)
    linarith
  have hrt_pos : a < (Set.Icc.reverse hab.le t : ℝ) := by
    change a < a + b - (t : ℝ)
    linarith
  by_cases hrs : (Set.Icc.reverse hab.le s : ℝ) < b
  · by_cases hrt : (Set.Icc.reverse hab.le t : ℝ) < b
    · exact (Set.Icc.involutive_reverse hab.le).injective (hinj hrs hrt hst)
    · have hrteq : Set.Icc.reverse hab.le t = ⟨b, hab.le, le_rfl⟩ := by
        apply Subtype.ext
        exact le_antisymm (Set.Icc.reverse hab.le t).property.2 (le_of_not_gt hrt)
      have hra : x (Set.Icc.reverse hab.le s) = x ⟨a, le_rfl, hab.le⟩ := by
        rw [hclosed, ← hrteq]
        exact hst
      have heq := hinj hrs hab hra
      exfalso
      have := congrArg Subtype.val heq
      linarith
  · have hrseq : Set.Icc.reverse hab.le s = ⟨b, hab.le, le_rfl⟩ := by
      apply Subtype.ext
      exact le_antisymm (Set.Icc.reverse hab.le s).property.2 (le_of_not_gt hrs)
    by_cases hrt : (Set.Icc.reverse hab.le t : ℝ) < b
    · have hra : x ⟨a, le_rfl, hab.le⟩ = x (Set.Icc.reverse hab.le t) := by
        rw [hclosed, ← hrseq]
        exact hst
      have heq := hinj hab hrt hra
      exfalso
      have := congrArg Subtype.val heq
      linarith
    · have hrteq : Set.Icc.reverse hab.le t = ⟨b, hab.le, le_rfl⟩ := by
        apply Subtype.ext
        exact le_antisymm (Set.Icc.reverse hab.le t).property.2 (le_of_not_gt hrt)
      exact (Set.Icc.involutive_reverse hab.le).injective (hrseq.trans hrteq.symm)

/-- Parameter reversal sends the reversed closed interval to the original interval image. -/
theorem image_Icc_reverse_interval {α : Type*} {a b : ℝ} (hab : a ≤ b)
    (x : Set.Icc a b → α) (l u : Set.Icc a b) (_hlu : l ≤ u) :
    (x ∘ Set.Icc.reverse hab) ''
        Set.Icc (Set.Icc.reverse hab u) (Set.Icc.reverse hab l) =
      x '' Set.Icc l u := by
  ext z
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨Set.Icc.reverse hab s, ?_, rfl⟩
    constructor
    · simpa only [Set.Icc.involutive_reverse hab l] using
        Set.Icc.antitone_reverse hab hs.2
    · simpa only [Set.Icc.involutive_reverse hab u] using
        Set.Icc.antitone_reverse hab hs.1
  · rintro ⟨s, hs, rfl⟩
    refine ⟨Set.Icc.reverse hab s, ?_, ?_⟩
    · constructor
      · exact Set.Icc.antitone_reverse hab hs.2
      · exact Set.Icc.antitone_reverse hab hs.1
    · simp only [Function.comp_apply, Set.Icc.involutive_reverse hab s]

-- Duplicate of the current private UpperGraph helper; promote to Geometry.Support.
private theorem exists_Icc_coe_image_of_compact_connected_Ioo {a b : ℝ}
    {S : Set (Set.Ioo a b)} (hS : IsCompact S) (hconn : IsConnected S) :
    ∃ l u : ℝ, ((fun t : Set.Ioo a b ↦ (t : ℝ)) '' S) = Set.Icc l u := by
  let T := (fun t : Set.Ioo a b ↦ (t : ℝ)) '' S
  have hTc : IsCompact T := hS.image continuous_subtype_val
  have hTconn : IsConnected T := hconn.image _ continuous_subtype_val.continuousOn
  exact ⟨sInf T, sSup T, eq_Icc_of_connected_compact hTconn hTc⟩

private theorem exists_Icc_pullback_of_compact_connected_puncturedLoop
    {a b : ℝ} {x : Set.Icc a b → Point} (hab : a ≤ b) (hab' : a < b)
    (hx : Continuous x)
    (hclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    (hinj : Set.InjOn x {t | (t : ℝ) < b})
    (C : Set (puncturedLoopRangeSet hab x)) (hC : IsCompact C)
    (hconn : IsConnected C) :
    ∃ l u : ℝ,
      (fun t : Set.Ioo a b ↦ (t : ℝ)) ''
          ((openIntervalHomeomorphPuncturedRange hab hab' x hx hclosed hinj).symm '' C) =
        Set.Icc l u := by
  let e := openIntervalHomeomorphPuncturedRange hab hab' x hx hclosed hinj
  exact exists_Icc_coe_image_of_compact_connected_Ioo
    (hC.image e.symm.continuous) (hconn.image e.symm e.symm.continuous.continuousOn)

private theorem exists_Icc_parameters_of_compact_pathConnected_subset_loop
    {a b : ℝ} {x : Set.Icc a b → Point} (hab : a ≤ b) (hab' : a < b)
    (hx : Continuous x)
    (hclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    (hinj : Set.InjOn x {t | (t : ℝ) < b})
    (C : Set Point) (hC : IsCompact C) (hpath : IsPathConnected C)
    (hCrange : C ⊆ Set.range x) (hbase : x ⟨a, le_rfl, hab⟩ ∉ C) :
    ∃ l u : ℝ,
      (fun t : Set.Ioo a b ↦ (t : ℝ)) ''
          ((openIntervalHomeomorphPuncturedRange hab hab' x hx hclosed hinj).symm ''
            {q : puncturedLoopRangeSet hab x | (q : Point) ∈ C}) = Set.Icc l u := by
  let D : Set (puncturedLoopRangeSet hab x) := {q | (q : Point) ∈ C}
  let f : puncturedLoopRangeSet hab x → Point := fun q ↦ q
  have hf_ind : Topology.IsInducing f :=
    Topology.IsInducing.comp Topology.IsEmbedding.subtypeVal.isInducing
      Topology.IsEmbedding.subtypeVal.isInducing
  have hCrange' : C ⊆ Set.range f := by
    intro p hp
    obtain ⟨t, ht⟩ := hCrange hp
    let q : Set.range x := ⟨p, ⟨t, ht⟩⟩
    have hq : (q : Point) ≠ x ⟨a, le_rfl, hab⟩ := by
      intro heq
      exact hbase (heq ▸ hp)
    exact ⟨⟨q, hq⟩, rfl⟩
  have hDcompact : IsCompact D := by
    change IsCompact (f ⁻¹' C)
    exact hf_ind.isCompact_preimage' hC hCrange'
  have hDrange : {q : Set.range x | (q : Point) ∈ C} ⊆ puncturedLoopRangeSet hab x := by
    intro q hq
    exact fun heq ↦ hbase (heq ▸ hq)
  have hDpath : IsPathConnected D := by
    have h₁ := hpath.preimage_coe hCrange
    exact h₁.preimage_coe hDrange
  exact exists_Icc_pullback_of_compact_connected_puncturedLoop hab hab' hx hclosed hinj
    D hDcompact hDpath.isConnected

private theorem exists_rectifiableOrientedArc_restrict_closedJordan_of_lt_top
    {a b : ℝ} {x : ContinuousBVPaths a b} {Γ : Set Point}
    (hab : a ≤ b) (hx : IsOrientedJordanParametrization hab Γ true x.val)
    (l u : Set.Icc a b) (hlu : l ≤ u) (hub : (u : ℝ) < b) :
    ∃ A : RectifiableOrientedArc,
      A.val.carrier = Set.range (ContinuousBVPaths.restrict x l u hlu).val ∧
      A.val.startPoint = x.val l ∧ A.val.endPoint = x.val u := by
  let y := ContinuousBVPaths.restrict x l u hlu
  have hyinj : Function.Injective y.val := by
    intro s t hst
    apply Subtype.ext
    have hs : (s : ℝ) < b := lt_of_le_of_lt s.property.2 hub
    have ht : (t : ℝ) < b := lt_of_le_of_lt t.property.2 hub
    have h := hx.2.2.2.2.2.1 hs ht hst
    exact congrArg (fun z : Set.Icc a b ↦ (z : ℝ)) h
  let A0 : OrientedJordanArc :=
    { carrier := Set.range y.val
      startPoint := x.val l
      endPoint := x.val u
      parametrizable := ⟨l, u, hlu, y.val, y.property.1, hyinj, rfl, rfl, rfl⟩ }
  let p : ArcBVParametrization A0 :=
    { a := l, b := u, ordered := hlu, path := y, injective := hyinj,
      range_eq := rfl, start_eq := rfl, end_eq := rfl }
  exact ⟨⟨A0, ⟨p⟩⟩, rfl, rfl, rfl⟩

/-- Convex interpolation between ordered interval points is strictly increasing. -/
theorem strictMono_convexComb_of_lt {a b : ℝ}
    (l u : Set.Icc a b) (hlu : l < u) : StrictMono (Set.Icc.convexComb l u) := by
  intro s t hst
  have hlu' : (l : ℝ) < u := hlu
  have hst' : (s : ℝ) < t := hst
  change (1 - (s : ℝ)) * l + (s : ℝ) * u <
    (1 - (t : ℝ)) * l + (t : ℝ) * u
  nlinarith [mul_pos (sub_pos.mpr hst') (sub_pos.mpr hlu')]

/-- The two closed pieces outside an interior parameter interval trace exactly the
closed curve with the open interval image removed. -/
theorem image_complement_interval_of_closed_injOn
    {α : Type*} {a b : ℝ} (hab : a ≤ b) (x : Set.Icc a b → α)
    (hclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    (hinj : Set.InjOn x {t | (t : ℝ) < b})
    (l u : Set.Icc a b) (hal : a < l) (hub : (u : ℝ) < b) :
    x '' {t | t ≤ l ∨ u ≤ t} =
      Set.range x \ x '' {t | l < t ∧ t < u} := by
  ext p
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨Set.mem_range_self t, ?_⟩
    rintro ⟨s, hs, heq⟩
    have hsb : (s : ℝ) < b := lt_trans hs.2 hub
    by_cases htb : (t : ℝ) < b
    · have hst := hinj hsb htb heq
      subst t
      exact ht.elim (not_le_of_gt hs.1) (not_le_of_gt hs.2)
    · have hte : t = ⟨b, hab, le_rfl⟩ := by
        apply Subtype.ext
        exact le_antisymm t.2.2 (le_of_not_gt htb)
      have hab' : a < b := hal.trans_le l.2.2
      have hsa : s = ⟨a, le_rfl, hab⟩ :=
        hinj hsb hab' (heq.trans ((congrArg x hte).trans hclosed.symm))
      have : (l : ℝ) < a := by
        have h := hs.1
        rw [hsa] at h
        exact h
      exact (not_lt_of_ge hal.le) this
  · rintro ⟨⟨t, rfl⟩, hp⟩
    refine ⟨t, ?_, rfl⟩
    by_contra ht
    have hs : l < t ∧ t < u := ⟨lt_of_not_ge (fun h ↦ ht (Or.inl h)),
      lt_of_not_ge (fun h ↦ ht (Or.inr h))⟩
    exact hp ⟨t, hs, rfl⟩

/-- Convex interpolation between the interval endpoints covers the interval. -/
theorem surjective_convexComb_endpoints (a b : ℝ) (hab : a ≤ b) :
    Function.Surjective
      (Set.Icc.convexComb (⟨a, le_rfl, hab⟩ : Set.Icc a b) ⟨b, hab, le_rfl⟩) := by
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
    · change (1 - ((x : ℝ) - a) / (b - a)) * a +
        ((x : ℝ) - a) / (b - a) * b = (x : ℝ)
      field_simp [ne_of_gt (sub_pos.mpr hab)]
      ring

/-- The initial restriction of a cyclically concatenated closed path traces the
complement of an interior parameter interval. -/
theorem range_cyclicConcat_restrict_to_complement
    {α : Type*} {a b : ℝ} (hab : a ≤ b) (f : Set.Icc a b → α)
    (hclosed : f ⟨a, le_rfl, hab⟩ = f ⟨b, hab, le_rfl⟩)
    (l u : Set.Icc a b) (hal : a < l) (hlu : l < u) (hub : (u : ℝ) < b)
    (θ : Set.Icc (0 : ℝ) 1)
    (hθ : Set.Icc.convexComb ⟨a, le_rfl, hab⟩ u θ = l) :
    let v : ℝ := 1 + θ
    Set.range (fun z : Set.Icc (0 : ℝ) v ↦
      Function.concatUnitIntervals
        (f ∘ Set.Icc.convexComb u ⟨b, hab, le_rfl⟩)
        (f ∘ Set.Icc.convexComb ⟨a, le_rfl, hab⟩ u)
        ⟨z, z.property.1, z.property.2.trans (by
          have hθle : (θ : ℝ) ≤ 1 := θ.property.2
          dsimp only [v]
          linarith)⟩) = f '' {z | z ≤ l ∨ u ≤ z} := by
  dsimp only
  ext p
  constructor
  · rintro ⟨z, rfl⟩
    by_cases hz : (z : ℝ) ≤ 1
    · let q : Set.Icc (0 : ℝ) 1 := ⟨z, z.property.1, hz⟩
      let y := Set.Icc.convexComb u ⟨b, hab, le_rfl⟩ q
      refine ⟨y, Or.inr ?_, ?_⟩
      · change (u : ℝ) ≤ (1 - (q : ℝ)) * u + (q : ℝ) * b
        nlinarith [q.property.1, q.property.2, u.property.2]
      · have hvnonneg : 0 ≤ 1 + (θ : ℝ) := by linarith [θ.property.1]
        have hzmem : (z : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨z.property.1, hz⟩
        change f y = Function.concatUnitIntervals _ _
          (⟨z, z.property.1, z.property.2.trans (by linarith [θ.property.2])⟩ :
            Set.Icc (0 : ℝ) 2)
        simp [Function.concatUnitIntervals, hz, q, y,
          Set.projIcc_of_mem (by norm_num) hzmem]
    · have hz1 : 1 < (z : ℝ) := lt_of_not_ge hz
      have hzsub0 : 0 ≤ (z : ℝ) - 1 := by linarith
      have hzsub1 : (z : ℝ) - 1 ≤ 1 := by
        have := z.property.2
        nlinarith [θ.property.2]
      let q : Set.Icc (0 : ℝ) 1 := ⟨(z : ℝ) - 1, hzsub0, hzsub1⟩
      let y := Set.Icc.convexComb ⟨a, le_rfl, hab⟩ u q
      refine ⟨y, Or.inl ?_, ?_⟩
      · have hzθ : (q : ℝ) ≤ θ := by
          dsimp only [q]
          linarith [z.property.2]
        change (1 - (q : ℝ)) * a + (q : ℝ) * u ≤ (l : ℝ)
        have hθval := congrArg Subtype.val hθ
        change (1 - (θ : ℝ)) * a + (θ : ℝ) * u = (l : ℝ) at hθval
        nlinarith [hzθ, le_of_lt (lt_trans hal hlu)]
      · simp [Function.concatUnitIntervals, hz, q, y,
          Set.projIcc_of_mem (by norm_num) ⟨hzsub0, hzsub1⟩]
  · rintro ⟨y, hy, rfl⟩
    rcases hy with hyl | huy
    · let y' : Set.Icc a (u : ℝ) := ⟨y, y.property.1, hyl.trans hlu.le⟩
      obtain ⟨q, hq'⟩ := surjective_convexComb_endpoints a u
        (le_trans l.property.1 hlu.le) y'
      have hq : Set.Icc.convexComb ⟨a, le_rfl, hab⟩ u q = y := by
        apply Subtype.ext
        have h := congrArg (fun z : Set.Icc a (u : ℝ) ↦ (z : ℝ)) hq'
        simpa only [Set.Icc.coe_convexComb] using h
      have hqθ : (q : ℝ) ≤ θ := by
        have hqval := congrArg Subtype.val hq
        have hθval := congrArg Subtype.val hθ
        change (1 - (q : ℝ)) * a + (q : ℝ) * u = (y : ℝ) at hqval
        change (1 - (θ : ℝ)) * a + (θ : ℝ) * u = (l : ℝ) at hθval
        have hau : a < (u : ℝ) := hal.trans hlu
        by_contra hn
        have hθq : (θ : ℝ) < q := lt_of_not_ge hn
        have hprod : 0 < ((q : ℝ) - θ) * ((u : ℝ) - a) :=
          mul_pos (sub_pos.mpr hθq) (sub_pos.mpr hau)
        have : (l : ℝ) < y := by nlinarith [hqval, hθval, hprod]
        exact (not_lt_of_ge hyl) this
      by_cases hq0 : (q : ℝ) = 0
      · let z : Set.Icc (0 : ℝ) (1 + (θ : ℝ)) := ⟨1, by
          constructor
          · norm_num
          · linarith [θ.property.1]⟩
        refine ⟨z, ?_⟩
        have hyA : y = ⟨a, le_rfl, hab⟩ := by
          apply Subtype.ext
          have hqval := congrArg (fun z : Set.Icc a b ↦ (z : ℝ)) hq
          change (1 - (q : ℝ)) * a + (q : ℝ) * u = (y : ℝ) at hqval
          simp [hq0] at hqval
          exact hqval.symm
        rw [hyA, hclosed]
        simp [z, Function.comp_def]
      · have hqpos : 0 < (q : ℝ) := lt_of_le_of_ne q.property.1 (Ne.symm hq0)
        let z : Set.Icc (0 : ℝ) (1 + (θ : ℝ)) := ⟨(q : ℝ) + 1, by
          constructor <;> linarith⟩
        refine ⟨z, ?_⟩
        have hznot : ¬(z : ℝ) ≤ 1 := by dsimp only [z]; linarith
        rw [← hq]
        simp [z, Function.concatUnitIntervals, hznot,
          Set.projIcc_of_mem (by norm_num) q.property]
    · let y' : Set.Icc (u : ℝ) b := ⟨y, huy, y.property.2⟩
      obtain ⟨q, hq'⟩ := surjective_convexComb_endpoints u b hub.le y'
      have hq : Set.Icc.convexComb u ⟨b, hab, le_rfl⟩ q = y := by
        apply Subtype.ext
        have h := congrArg (fun z : Set.Icc (u : ℝ) b ↦ (z : ℝ)) hq'
        simpa only [Set.Icc.coe_convexComb] using h
      let z : Set.Icc (0 : ℝ) (1 + (θ : ℝ)) := ⟨q, by
        constructor
        · exact q.property.1
        · linarith [q.property.2, θ.property.1]⟩
      refine ⟨z, ?_⟩
      have hzle : (z : ℝ) ≤ 1 := q.property.2
      rw [← hq]
      simp [z, Function.concatUnitIntervals, hzle,
        Set.projIcc_of_mem (by norm_num) q.property]

private theorem exists_complementary_rectifiableOrientedArc
    {a b : ℝ} {x : ContinuousBVPaths a b} {Γ : Set Point}
    (hab : a ≤ b) (hx : IsOrientedJordanParametrization hab Γ true x.val)
    (l u : Set.Icc a b) (hal : a < l) (hlu : l < u) (hub : (u : ℝ) < b)
    (P Q : Point) (hlQ : x.val l = Q) (huP : x.val u = P) :
    ∃ A : RectifiableOrientedArc,
      A.val.carrier = Set.range x.val \ x.val '' {z | l < z ∧ z < u} ∧
      A.val.startPoint = P ∧ A.val.endPoint = Q := by
  let l' : Set.Icc a (u : ℝ) := ⟨l, l.property.1, hlu.le⟩
  obtain ⟨θ, hθ'⟩ := surjective_convexComb_endpoints a u
    (le_trans l.property.1 hlu.le) l'
  have hθ : Set.Icc.convexComb ⟨a, le_rfl, hab⟩ u θ = l := by
    apply Subtype.ext
    have h := congrArg (fun z : Set.Icc a (u : ℝ) ↦ (z : ℝ)) hθ'
    simpa only [Set.Icc.coe_convexComb] using h
  have hθpos : 0 < (θ : ℝ) := by
    by_contra hn
    have hθzero : (θ : ℝ) = 0 := le_antisymm (le_of_not_gt hn) θ.property.1
    have h := congrArg (fun z : Set.Icc a b ↦ (z : ℝ)) hθ
    change (1 - (θ : ℝ)) * a + (θ : ℝ) * u = (l : ℝ) at h
    simp [hθzero] at h
    linarith
  have hθlt : (θ : ℝ) < 1 := by
    by_contra hn
    have hθone : (θ : ℝ) = 1 := le_antisymm θ.property.2 (le_of_not_gt hn)
    have h := congrArg (fun z : Set.Icc a b ↦ (z : ℝ)) hθ
    change (1 - (θ : ℝ)) * a + (θ : ℝ) * u = (l : ℝ) at h
    simp [hθone] at h
    exact hlu.ne (Subtype.ext h.symm)
  obtain ⟨r, hrJordan, hr⟩ :=
    exists_oriented_cyclic_rotation_eq_concat hab x hx u
      (hal.trans hlu) hub
  let z : Set.Icc (0 : ℝ) 2 := ⟨0, by norm_num⟩
  let v : Set.Icc (0 : ℝ) 2 := ⟨1 + (θ : ℝ), by
    constructor <;> linarith⟩
  have hzv : z ≤ v := by change (0 : ℝ) ≤ 1 + θ; linarith
  have hvtop : (v : ℝ) < 2 := by dsimp only [v]; linarith
  obtain ⟨A, hAcarrier, hAstart, hAend⟩ :=
    exists_rectifiableOrientedArc_restrict_closedJordan_of_lt_top
      (a := 0) (b := 2) (x := r) (Γ := Γ) (by norm_num) hrJordan z v hzv hvtop
  have hrzero : r.val z = P := by
    rw [hr]
    simp [z, Function.comp_def, huP]
  have hrv : r.val v = Q := by
    rw [hr]
    have hvnot : ¬(v : ℝ) ≤ 1 := by dsimp only [v]; linarith
    have hθmem : (θ : ℝ) ∈ Set.Icc (0 : ℝ) 1 := θ.property
    have hproj : Set.projIcc (0 : ℝ) 1 (by norm_num) ((v : ℝ) - 1) = θ := by
      apply Subtype.ext
      simp [v]
    simp [Function.concatUnitIntervals, hvnot, hproj, hθ, hlQ]
  refine ⟨A, ?_, hAstart.trans hrzero, hAend.trans hrv⟩
  rw [hAcarrier]
  have hrange : Set.range (ContinuousBVPaths.restrict r z v hzv).val =
      Set.range (fun w : Set.Icc (0 : ℝ) (1 + (θ : ℝ)) ↦
        Function.concatUnitIntervals
          (x.val ∘ Set.Icc.convexComb u ⟨b, hab, le_rfl⟩)
          (x.val ∘ Set.Icc.convexComb ⟨a, le_rfl, hab⟩ u)
          ⟨w, w.property.1, w.property.2.trans (by linarith [θ.property.2])⟩) := by
    change Set.range (r.val ∘ fun w : Set.Icc (0 : ℝ) (v : ℝ) ↦
      (⟨w, w.property.1, w.property.2.trans v.property.2⟩ : Set.Icc (0 : ℝ) 2)) = _
    rw [hr]
    rfl
  rw [hrange, range_cyclicConcat_restrict_to_complement hab x.val
    hx.2.2.2.2.1 l u hal hlu hub θ hθ]
  exact image_complement_interval_of_closed_injOn hab x.val hx.2.2.2.2.1
    hx.2.2.2.2.2.1 l u hal hub

/-- If a closed parameter interval traces a nondegenerate segment injectively, its
open interval traces the segment with its endpoints removed. -/
theorem image_Ioo_eq_segment_diff_endpoints_of_image_Icc
    {a b : ℝ} {x : Set.Icc a b → Point}
    (hinj : Set.InjOn x {t | (t : ℝ) < b})
    (l u : Set.Icc a b) (hlu : l < u) (hub : (u : ℝ) < b)
    (P Q : Point) (hl : x l = Q) (hu : x u = P)
    (himage : x '' Set.Icc l u = segment ℝ P Q) :
    x '' {z | l < z ∧ z < u} = segment ℝ P Q \ {P, Q} := by
  apply Set.Subset.antisymm
  · rintro p ⟨z, hz, rfl⟩
    refine ⟨himage ▸ ⟨z, ⟨hz.1.le, hz.2.le⟩, rfl⟩, ?_⟩
    intro hp
    rcases hp with hp | hp
    · have hzu := hinj (show (z : ℝ) < b from lt_trans hz.2 hub) hub
        (hp.trans hu.symm)
      exact (ne_of_lt hz.2) hzu
    · have hzl := hinj (show (z : ℝ) < b from lt_trans hz.2 hub)
        (show (l : ℝ) < b from lt_trans hlu hub) (hp.trans hl.symm)
      exact (ne_of_gt hz.1) hzl
  · rintro p ⟨hpseg, hpends⟩
    rw [← himage] at hpseg
    obtain ⟨z, hz, rfl⟩ := hpseg
    refine ⟨z, ⟨?_, ?_⟩, rfl⟩
    · refine lt_of_le_of_ne hz.1 ?_
      intro h
      apply hpends
      exact Or.inr ((congrArg x h).symm.trans hl)
    · refine lt_of_le_of_ne hz.2 ?_
      intro h
      apply hpends
      exact Or.inl ((congrArg x h).trans hu)

private theorem exists_rectifiableOrientedArc_of_cut_parametrization
    {a b : ℝ} {x : ContinuousBVPaths a b} {Γ U : Set Point}
    (hab : a ≤ b) (hx : IsOrientedJordanParametrization hab Γ true x.val)
    (l u : Set.Icc a b) (hal : a < l) (hlu : l < u) (hub : (u : ℝ) < b)
    (P Q : Point) (hl : x.val l = Q) (hu : x.val u = P)
    (hfrontier : Γ = U ∪ segment ℝ P Q)
    (hinter : U ∩ segment ℝ P Q = {P, Q})
    (himage : x.val '' Set.Icc l u = segment ℝ P Q) :
    ∃ A : RectifiableOrientedArc,
      A.val.carrier = U ∧ A.val.startPoint = P ∧ A.val.endPoint = Q := by
  obtain ⟨A, hA, hstart, hend⟩ :=
    exists_complementary_rectifiableOrientedArc hab hx l u hal hlu hub P Q hl hu
  refine ⟨A, ?_, hstart, hend⟩
  rw [hA, hx.2.2.2.1, hfrontier,
    image_Ioo_eq_segment_diff_endpoints_of_image_Icc
      hx.2.2.2.2.2.1 l u hlu hub P Q hl hu himage]
  ext p
  constructor
  · rintro ⟨hp, hpnot⟩
    rcases hp with hpU | hpseg
    · exact hpU
    · have hpends : p ∈ ({P, Q} : Set Point) := by
        by_contra hn
        exact hpnot ⟨hpseg, hn⟩
      rw [← hinter] at hpends
      exact hpends.1
  · intro hpU
    refine ⟨Or.inl hpU, ?_⟩
    rintro ⟨hpseg, hpnotends⟩
    apply hpnotends
    rw [← hinter]
    exact ⟨hpU, hpseg⟩

/-- A nondegenerate segment in a closed Jordan curve, away from the base point,
is traced by an interior parameter interval. -/
theorem exists_parameter_interval_of_segment_subset_closedJordan
    {a b : ℝ} {x : ContinuousBVPaths a b} {Γ : Set Point}
    (hab : a < b) (hx : IsOrientedJordanParametrization hab.le Γ true x.val)
    (P Q : Point) (hPQ : P ≠ Q) (hsegment : segment ℝ P Q ⊆ Γ)
    (hbase : x.val ⟨a, le_rfl, hab.le⟩ ∉ segment ℝ P Q) :
    ∃ l u : Set.Icc a b, a < l ∧ l < u ∧ (u : ℝ) < b ∧
      x.val '' Set.Icc l u = segment ℝ P Q := by
  have hcompact : IsCompact (segment ℝ P Q) := by
    rw [segment_eq_image]
    exact isCompact_Icc.image (by fun_prop)
  have hpath : IsPathConnected (segment ℝ P Q) :=
    (convex_segment P Q).isPathConnected ⟨P, left_mem_segment ℝ P Q⟩
  have hCrange : segment ℝ P Q ⊆ Set.range x.val := by
    rw [hx.2.2.2.1]
    exact hsegment
  obtain ⟨l, u, hlu⟩ := exists_Icc_parameters_of_compact_pathConnected_subset_loop
    hab.le hab x.property.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1
    (segment ℝ P Q) hcompact hpath hCrange hbase
  have hpre_nonempty :
      ((openIntervalHomeomorphPuncturedRange hab.le hab x.val x.property.1
        hx.2.2.2.2.1 hx.2.2.2.2.2.1).symm ''
        {q : puncturedLoopRangeSet hab.le x.val | (q : Point) ∈ segment ℝ P Q}).Nonempty := by
    let q : Set.range x.val := ⟨P, hCrange (left_mem_segment ℝ P Q)⟩
    have hq : (q : Point) ≠ x.val ⟨a, le_rfl, hab.le⟩ := by
      intro heq
      exact hbase (heq ▸ left_mem_segment ℝ P Q)
    let q' : puncturedLoopRangeSet hab.le x.val := ⟨q, hq⟩
    refine ⟨(openIntervalHomeomorphPuncturedRange hab.le hab x.val x.property.1
      hx.2.2.2.2.1 hx.2.2.2.2.2.1).symm q', ?_⟩
    exact ⟨q', left_mem_segment ℝ P Q, rfl⟩
  have hIcc_nonempty : (Set.Icc l u).Nonempty := by
    rw [← hlu]
    exact hpre_nonempty.image _
  have hlu_order : l ≤ u := Set.nonempty_Icc.mp hIcc_nonempty
  have hlmem : l ∈ Set.Icc l u := ⟨le_rfl, hlu_order⟩
  have humem : u ∈ Set.Icc l u := ⟨hlu_order, le_rfl⟩
  rw [← hlu] at hlmem humem
  obtain ⟨sl, hsl, hslval⟩ := hlmem
  obtain ⟨su, hsu, hsuval⟩ := humem
  change (sl : ℝ) = l at hslval
  change (su : ℝ) = u at hsuval
  let l' : Set.Icc a b := ⟨sl, sl.property.1.le, sl.property.2.le⟩
  let u' : Set.Icc a b := ⟨su, su.property.1.le, su.property.2.le⟩
  have hlstrict : a < (l' : ℝ) := sl.property.1
  have hustricttop : (u' : ℝ) < b := su.property.2
  have hlu' : l' ≤ u' := by
    change (sl : ℝ) ≤ su
    linarith
  have himage : x.val '' Set.Icc l' u' = segment ℝ P Q := by
    apply Set.Subset.antisymm
    · rintro p ⟨s, hs, rfl⟩
      let si : Set.Ioo a b := ⟨s, lt_of_lt_of_le hlstrict hs.1,
        lt_of_le_of_lt hs.2 hustricttop⟩
      have hscoord : (s : ℝ) ∈
          (fun z : Set.Ioo a b ↦ (z : ℝ)) ''
            ((openIntervalHomeomorphPuncturedRange hab.le hab x.val x.property.1
              hx.2.2.2.2.1 hx.2.2.2.2.2.1).symm ''
              {q : puncturedLoopRangeSet hab.le x.val |
                (q : Point) ∈ segment ℝ P Q}) := by
        rw [hlu]
        change l ≤ (s : ℝ) ∧ (s : ℝ) ≤ u
        constructor
        · calc l = (sl : ℝ) := hslval.symm
               _ ≤ s := hs.1
        · calc (s : ℝ) ≤ su := hs.2
               _ = u := hsuval
      obtain ⟨z, hz, hzval⟩ := hscoord
      obtain ⟨q, hqseg, hzq⟩ := hz
      have hzcoe := openIntervalHomeomorphPuncturedRange_coe hab.le hab x.val
        x.property.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 z
      have hzs : z = si := Subtype.ext hzval
      rw [hzs] at hzcoe hzq
      let e := openIntervalHomeomorphPuncturedRange hab.le hab x.val x.property.1
        hx.2.2.2.2.1 hx.2.2.2.2.2.1
      have heq : e si = q := by
        exact e.eq_symm_apply.mp hzq.symm
      have heq' := congrArg (fun z : puncturedLoopRangeSet hab.le x.val ↦ (z : Point)) heq
      rw [hzcoe] at heq'
      change (q : Point) ∈ segment ℝ P Q at hqseg
      have heq'' : x.val s = (q : Point) := by simpa [si] using heq'
      rw [heq'']
      exact hqseg
    · intro p hp
      let q : Set.range x.val := ⟨p, hCrange hp⟩
      have hqbase : (q : Point) ≠ x.val ⟨a, le_rfl, hab.le⟩ := by
        intro heq
        exact hbase (heq ▸ hp)
      let q' : puncturedLoopRangeSet hab.le x.val := ⟨q, hqbase⟩
      let s := (openIntervalHomeomorphPuncturedRange hab.le hab x.val x.property.1
        hx.2.2.2.2.1 hx.2.2.2.2.2.1).symm q'
      have hscoord : (s : ℝ) ∈ Set.Icc l u := by
        rw [← hlu]
        exact ⟨s, ⟨q', hp, rfl⟩, rfl⟩
      let s' : Set.Icc a b := ⟨s, s.property.1.le, s.property.2.le⟩
      refine ⟨s', ?_, ?_⟩
      · change l' ≤ s' ∧ s' ≤ u'
        constructor <;> change (_ : ℝ) ≤ _ <;> dsimp only [l', u', s'] <;>
          linarith [hscoord.1, hscoord.2]
      have hscoe := openIntervalHomeomorphPuncturedRange_coe hab.le hab x.val
        x.property.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 s
      let e := openIntervalHomeomorphPuncturedRange hab.le hab x.val x.property.1
        hx.2.2.2.2.1 hx.2.2.2.2.2.1
      have heq : e s = q' := e.apply_symm_apply q'
      have heq' := congrArg (fun z : puncturedLoopRangeSet hab.le x.val ↦ (z : Point)) heq
      exact hscoe.symm.trans heq'
  have hlune : l' ≠ u' := by
    intro heq
    have hsingle : segment ℝ P Q = {x.val l'} := by
      rw [← himage, heq, Set.Icc_self, Set.image_singleton]
    have hPm : P ∈ ({x.val l'} : Set Point) := hsingle ▸ left_mem_segment ℝ P Q
    have hQm : Q ∈ ({x.val l'} : Set Point) := hsingle ▸ right_mem_segment ℝ P Q
    exact hPQ (by simpa using hPm.trans hQm.symm)
  exact ⟨l', u', hlstrict, lt_of_le_of_ne hlu' hlune,
    hustricttop, himage⟩

private theorem inner_sub_right_injOn_segment (P Q : Point) (hPQ : P ≠ Q) :
    Set.InjOn (fun p : Point ↦ inner ℝ (p - P) (Q - P)) (segment ℝ P Q) := by
  intro p hp q hq hpq
  rw [segment_eq_image' ℝ P Q] at hp hq
  obtain ⟨s, hs, rfl⟩ := hp
  obtain ⟨t, ht, rfl⟩ := hq
  have hd : Q - P ≠ 0 := sub_ne_zero.mpr hPQ.symm
  have hnorm : 0 < ‖Q - P‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hd)
  have hst : s = t := by
    simp only [add_sub_cancel_left, inner_smul_left, real_inner_self_eq_norm_sq] at hpq
    have hpq' : s * ‖Q - P‖ ^ 2 = t * ‖Q - P‖ ^ 2 := by simpa using hpq
    nlinarith
  rw [hst]

private theorem exists_rectifiableOrientedArc_reverse (A : RectifiableOrientedArc) :
    ∃ B : RectifiableOrientedArc,
      B.val.carrier = A.val.carrier ∧ B.val.startPoint = A.val.endPoint ∧
        B.val.endPoint = A.val.startPoint := by
  let p := Classical.choice A.property
  let r := Set.Icc.reverse p.ordered
  let y : ContinuousBVPaths p.a p.b :=
    ⟨p.path.val ∘ r, p.path.property.1.comp (Set.Icc.continuous_reverse p.ordered),
      fun i ↦ BoundedVariationOn.comp_antitone_surjective_Icc p.ordered
        (p.path.property.2 i) (Set.Icc.antitone_reverse p.ordered)
          (Set.Icc.surjective_reverse p.ordered)⟩
  have hyinj : Function.Injective y.val :=
    p.injective.comp (Set.Icc.involutive_reverse p.ordered).injective
  have hyrange : Set.range y.val = A.val.carrier := by
    have hrange : Set.range y.val = Set.range p.path.val := by
      apply Set.Subset.antisymm
      · rintro z ⟨t, rfl⟩
        exact ⟨r t, rfl⟩
      · rintro z ⟨t, rfl⟩
        obtain ⟨s, hs⟩ := Set.Icc.surjective_reverse p.ordered t
        refine ⟨s, ?_⟩
        change p.path.val (r s) = p.path.val t
        rw [show r s = t by exact hs]
    rw [hrange]
    exact p.range_eq
  have hystart : y.val ⟨p.a, le_rfl, p.ordered⟩ = A.val.endPoint := by
    simpa [y, r, Set.Icc.reverse] using p.end_eq
  have hyend : y.val ⟨p.b, p.ordered, le_rfl⟩ = A.val.startPoint := by
    simpa [y, r, Set.Icc.reverse] using p.start_eq
  let B0 : OrientedJordanArc :=
    { carrier := A.val.carrier
      startPoint := A.val.endPoint
      endPoint := A.val.startPoint
      parametrizable := ⟨p.a, p.b, p.ordered, y.val, y.property.1, hyinj,
        hyrange, hystart, hyend⟩ }
  let q : ArcBVParametrization B0 :=
    { a := p.a
      b := p.b
      ordered := p.ordered
      path := y
      injective := hyinj
      range_eq := hyrange
      start_eq := hystart
      end_eq := hyend }
  exact ⟨⟨B0, ⟨q⟩⟩, rfl, rfl, rfl⟩

/-- The endpoints of an injectively parametrized nondegenerate segment are the
parameter-interval endpoints, in one of the two possible orders. -/
theorem endpoints_eq_or_eq_swap_of_image_Icc_eq_segment
    {a b : ℝ} {x : ContinuousBVPaths a b}
    (hab : a ≤ b) (hinj : Set.InjOn x.val {t | (t : ℝ) < b})
    (l u : Set.Icc a b) (hlu : l < u) (hub : (u : ℝ) < b)
    (P Q : Point) (hPQ : P ≠ Q)
    (himage : x.val '' Set.Icc l u = segment ℝ P Q) :
    (x.val l = P ∧ x.val u = Q) ∨ (x.val l = Q ∧ x.val u = P) := by
  let f : ℝ → ℝ := fun t ↦
    inner ℝ (x.val (Set.projIcc a b hab t) - P) (Q - P)
  have hf_cont : Continuous f := by
    exact (x.property.1.comp continuous_projIcc).sub continuous_const |>.inner
      continuous_const
  have hproj (t : ℝ) (ht : t ∈ Set.Icc (l : ℝ) u) :
      Set.projIcc a b hab t =
        ⟨t, l.property.1.trans ht.1, ht.2.trans u.property.2⟩ := by
    exact Set.projIcc_of_mem hab ⟨l.property.1.trans ht.1, ht.2.trans u.property.2⟩
  have hparam (t : ℝ) (ht : t ∈ Set.Icc (l : ℝ) u) :
      x.val (Set.projIcc a b hab t) ∈ segment ℝ P Q := by
    rw [← himage]
    refine ⟨⟨t, l.property.1.trans ht.1, ht.2.trans u.property.2⟩, ?_, ?_⟩
    · exact ht
    · apply congrArg x.val
      apply Subtype.ext
      exact congrArg Subtype.val (hproj t ht).symm
  have hf_inj : Set.InjOn f (Set.Icc (l : ℝ) u) := by
    intro s hs t ht hst
    have hxs := inner_sub_right_injOn_segment P Q hPQ
      (hparam s hs) (hparam t ht) hst
    have hst' := hinj
      (show ((Set.projIcc a b hab s : Set.Icc a b) : ℝ) < b by
        simpa [hproj s hs] using lt_of_le_of_lt hs.2 hub)
      (show ((Set.projIcc a b hab t : Set.Icc a b) : ℝ) < b by
        simpa [hproj t ht] using lt_of_le_of_lt ht.2 hub)
      hxs
    simpa [hproj s hs, hproj t ht] using congrArg Subtype.val hst'
  have hmono := ContinuousOn.strictMonoOn_of_injOn_Icc'
    (show (l : ℝ) ≤ u from hlu.le) hf_cont.continuousOn hf_inj
  have hP : P ∈ x.val '' Set.Icc l u := himage ▸ left_mem_segment ℝ P Q
  have hQ : Q ∈ x.val '' Set.Icc l u := himage ▸ right_mem_segment ℝ P Q
  obtain ⟨s, hs, hsP⟩ := hP
  obtain ⟨t, ht, htQ⟩ := hQ
  have hs' : (s : ℝ) ∈ Set.Icc (l : ℝ) u := hs
  have ht' : (t : ℝ) ∈ Set.Icc (l : ℝ) u := ht
  have hl' : (l : ℝ) ∈ Set.Icc (l : ℝ) u := ⟨le_rfl, hlu.le⟩
  have hu' : (u : ℝ) ∈ Set.Icc (l : ℝ) u := ⟨hlu.le, le_rfl⟩
  rcases hmono with hmono | hanti
  · left
    constructor
    · have hfls : f l ≤ f s := hmono.monotoneOn hl' hs' hs.1
      have hflP : f l = f s := by
        have hnonneg : 0 ≤ f l := by
          have hmem := hparam l hl'
          rw [segment_eq_image' ℝ P Q] at hmem
          obtain ⟨r, hr, hrl⟩ := hmem
          dsimp only [f]
          rw [← hrl]
          simp only [add_sub_cancel_left, inner_smul_left,
            real_inner_self_eq_norm_sq]
          exact mul_nonneg hr.1 (sq_nonneg _)
        have hfs : f s = 0 := by simp [f, hproj s hs', hsP]
        linarith
      simpa [hproj l hl'] using
        (inner_sub_right_injOn_segment P Q hPQ
          (hparam l hl') (hparam s hs') hflP |>.trans
            (by simpa [hproj s hs'] using hsP))
    · have hftu : f t ≤ f u := hmono.monotoneOn ht' hu' ht.2
      have hfuQ : f u = f t := by
        have hupper : f u ≤ ‖Q - P‖ ^ 2 := by
          have hmem := hparam u hu'
          rw [segment_eq_image' ℝ P Q] at hmem
          obtain ⟨r, hr, hru⟩ := hmem
          dsimp only [f]
          rw [← hru]
          simp only [add_sub_cancel_left, inner_smul_left,
            real_inner_self_eq_norm_sq]
          exact mul_le_of_le_one_left (sq_nonneg _) hr.2
        have hft : f t = ‖Q - P‖ ^ 2 := by
          simp [f, hproj t ht', htQ]
        linarith
      simpa [hproj u hu'] using
        (inner_sub_right_injOn_segment P Q hPQ
          (hparam u hu') (hparam t ht') hfuQ |>.trans
            (by simpa [hproj t ht'] using htQ))
  · right
    constructor
    · have hftl : f t ≤ f l := hanti.antitoneOn hl' ht' ht.1
      have hflQ : f l = f t := by
        have hupper : f l ≤ ‖Q - P‖ ^ 2 := by
          have hmem := hparam l hl'
          rw [segment_eq_image' ℝ P Q] at hmem
          obtain ⟨r, hr, hrl⟩ := hmem
          dsimp only [f]
          rw [← hrl]
          simp only [add_sub_cancel_left, inner_smul_left,
            real_inner_self_eq_norm_sq]
          exact mul_le_of_le_one_left (sq_nonneg _) hr.2
        have hft : f t = ‖Q - P‖ ^ 2 := by
          simp [f, hproj t ht', htQ]
        linarith
      simpa [hproj l hl'] using
        (inner_sub_right_injOn_segment P Q hPQ
          (hparam l hl') (hparam t ht') hflQ |>.trans
            (by simpa [hproj t ht'] using htQ))
    · have hfus : f u ≤ f s := hanti.antitoneOn hs' hu' hs.2
      have hfuP : f u = f s := by
        have hnonneg : 0 ≤ f u := by
          have hmem := hparam u hu'
          rw [segment_eq_image' ℝ P Q] at hmem
          obtain ⟨r, hr, hru⟩ := hmem
          dsimp only [f]
          rw [← hru]
          simp only [add_sub_cancel_left, inner_smul_left,
            real_inner_self_eq_norm_sq]
          exact mul_nonneg hr.1 (sq_nonneg _)
        have hfs : f s = 0 := by simp [f, hproj s hs', hsP]
        linarith
      simpa [hproj u hu'] using
        (inner_sub_right_injOn_segment P Q hPQ
          (hparam u hu') (hparam s hs') hfuP |>.trans
            (by simpa [hproj s hs'] using hsP))

/-- Removing a supporting chord from a counterclockwise closed Jordan path yields the oriented
complementary arc. -/
theorem exists_rectifiableOrientedArc_of_closedJordan_cut
    {a b : ℝ} {x : ContinuousBVPaths a b} {Γ U : Set Point}
    (hab : a < b) (hx : IsOrientedJordanParametrization hab.le Γ true x.val)
    (P Q : Point) (hPQ : P ≠ Q)
    (hbase : x.val ⟨a, le_rfl, hab.le⟩ ∉ segment ℝ P Q)
    (hfrontier : Γ = U ∪ segment ℝ P Q)
    (hinter : U ∩ segment ℝ P Q = {P, Q}) :
    ∃ A : RectifiableOrientedArc,
      A.val.carrier = U ∧ A.val.startPoint = P ∧ A.val.endPoint = Q := by
  have hsegment : segment ℝ P Q ⊆ Γ := by
    rw [hfrontier]
    exact Set.subset_union_right
  obtain ⟨l, u, hal, hlu, hub, himage⟩ :=
    exists_parameter_interval_of_segment_subset_closedJordan hab hx P Q hPQ hsegment hbase
  rcases endpoints_eq_or_eq_swap_of_image_Icc_eq_segment hab.le
      hx.2.2.2.2.2.1 l u hlu hub P Q hPQ himage with hend | hend
  · have hfrontier' : Γ = U ∪ segment ℝ Q P := by
      simpa only [segment_symm ℝ Q P] using hfrontier
    have hinter' : U ∩ segment ℝ Q P = {Q, P} := by
      rw [segment_symm ℝ Q P, hinter]
      exact Set.pair_comm P Q
    have himage' : x.val '' Set.Icc l u = segment ℝ Q P := by
      simpa only [segment_symm ℝ Q P] using himage
    obtain ⟨A, hA, hstart, hend'⟩ :=
      exists_rectifiableOrientedArc_of_cut_parametrization hab.le hx l u hal hlu hub
        Q P hend.1 hend.2 hfrontier' hinter' himage'
    obtain ⟨B, hB, hBstart, hBend⟩ := exists_rectifiableOrientedArc_reverse A
    exact ⟨B, hB.trans hA, hBstart.trans hend', hBend.trans hstart⟩
  · exact exists_rectifiableOrientedArc_of_cut_parametrization hab.le hx l u hal hlu hub
      P Q hend.1 hend.2 hfrontier hinter himage

end MovingSofa
