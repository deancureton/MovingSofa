import MovingSofa.Curve.Jordan.Subarc
import MovingSofa.Curve.SegmentAreaProperties

noncomputable section

namespace MovingSofa

open Set
/-- A proper restriction of a closed BV Jordan parametrization realizes an arc with the same
signed area as the restricted path. -/
theorem exists_rectifiableOrientedArc_restrict_closedJordan_with_area
    {a b : ℝ} {x : ContinuousBVPaths a b} {Γ : Set Point}
    (hab : a ≤ b) (hx : IsOrientedJordanParametrization hab Γ true x.val)
    (l u : Set.Icc a b) (hlu : l ≤ u) (hub : (u : ℝ) < b) :
    ∃ A : RectifiableOrientedArc,
      A.val.carrier = Set.range (ContinuousBVPaths.restrict x l u hlu).val ∧
      A.val.startPoint = x.val l ∧ A.val.endPoint = x.val u ∧
      jordanArcArea A =
        curveAreaFunctional (ContinuousBVPaths.restrict x l u hlu) := by
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
  let A : RectifiableOrientedArc := ⟨A0, ⟨p⟩⟩
  refine ⟨A, rfl, rfl, rfl, ?_⟩
  change curveAreaFunctional (Classical.choice A.property).path = curveAreaFunctional y
  exact (curveArea_reparametrization.2.1 A0 A0
    (Classical.choice A.property) p rfl).1 rfl rfl

/-- The suffix of the cyclic rotation, after the complementary arc, is an increasing
reparametrization of the removed interval. -/
theorem curveArea_cyclicSuffix_eq_restriction
    {a b : ℝ} (hab : a ≤ b) (x : ContinuousBVPaths a b)
    (l u : Set.Icc a b) (hal : a < l) (hlu : l < u)
    (θ : Set.Icc (0 : ℝ) 1)
    (hθ : Set.Icc.convexComb ⟨a, le_rfl, hab⟩ u θ = l)
    (r : ContinuousBVPaths 0 2)
    (hr : r.val = Function.concatUnitIntervals
      (x.val ∘ Set.Icc.convexComb u ⟨b, hab, le_rfl⟩)
      (x.val ∘ Set.Icc.convexComb ⟨a, le_rfl, hab⟩ u)) :
    let v : Set.Icc (0 : ℝ) 2 := ⟨1 + (θ : ℝ), by
      constructor <;> linarith [θ.property.1, θ.property.2]⟩
    curveAreaFunctional (ContinuousBVPaths.restrict r v ⟨2, by norm_num⟩ v.property.2) =
      curveAreaFunctional (ContinuousBVPaths.restrict x l u hlu.le) := by
  let v : Set.Icc (0 : ℝ) 2 := ⟨1 + (θ : ℝ), by
    constructor <;> linarith [θ.property.1, θ.property.2]⟩
  change curveAreaFunctional (ContinuousBVPaths.restrict r v ⟨2, by norm_num⟩
      v.property.2) =
    curveAreaFunctional (ContinuousBVPaths.restrict x l u hlu.le)
  have hθlt : (θ : ℝ) < 1 := by
    by_contra hn
    have hθone : (θ : ℝ) = 1 := le_antisymm θ.property.2 (le_of_not_gt hn)
    have h := congrArg Subtype.val hθ
    change (1 - (θ : ℝ)) * a + (θ : ℝ) * u = (l : ℝ) at h
    simp [hθone] at h
    exact hlu.ne (Subtype.ext h.symm)
  have hθpos_suffix : 0 < (θ : ℝ) := by
    by_contra hn
    have hθzero : (θ : ℝ) = 0 := le_antisymm (le_of_not_gt hn) θ.property.1
    have h := congrArg Subtype.val hθ
    change (1 - (θ : ℝ)) * a + (θ : ℝ) * u = (l : ℝ) at h
    simp [hθzero] at h
    linarith
  have hvlt : (v : ℝ) < 2 := by dsimp only [v]; linarith
  let ψ : Set.Icc (v : ℝ) 2 → Set.Icc (0 : ℝ) 1 := fun w ↦
    ⟨((w : ℝ) - (v : ℝ)) / (2 - (v : ℝ)), by
      constructor
      · exact div_nonneg (sub_nonneg.mpr w.property.1) (sub_nonneg.mpr hvlt.le)
      · exact (div_le_one (sub_pos.mpr hvlt)).2
          (sub_le_sub_right w.property.2 (v : ℝ))⟩
  let φ : Set.Icc (v : ℝ) 2 → Set.Icc (l : ℝ) u := fun w ↦
    Set.Icc.convexComb (⟨l, le_rfl, hlu.le⟩ : Set.Icc (l : ℝ) u)
      ⟨u, hlu.le, le_rfl⟩ (ψ w)
  have hψc : Continuous ψ := by
    apply Continuous.subtype_mk
    fun_prop
  have hψm : Monotone ψ := by
    intro s t hst
    apply Subtype.coe_le_coe.mp
    dsimp only [ψ]
    exact div_le_div_of_nonneg_right
      (sub_le_sub_right (show (s : ℝ) ≤ t from hst) _) (sub_nonneg.mpr hvlt.le)
  have hψs : Function.Surjective ψ := by
    intro q
    let w : Set.Icc (v : ℝ) 2 := ⟨(v : ℝ) + (2 - (v : ℝ)) * (q : ℝ), by
      constructor
      · nlinarith [q.property.1, sub_pos.mpr hvlt]
      · nlinarith [q.property.2, sub_pos.mpr hvlt]⟩
    refine ⟨w, Subtype.ext ?_⟩
    dsimp only [ψ, w]
    field_simp [ne_of_gt (sub_pos.mpr hvlt)]
    ring
  have hφc : Continuous φ :=
    (Set.Icc.continuous_convexComb _ _).comp hψc
  have hφm : Monotone φ := by
    intro s t hst
    change (1 - (ψ s : ℝ)) * (l : ℝ) + (ψ s : ℝ) * (u : ℝ) ≤
      (1 - (ψ t : ℝ)) * (l : ℝ) + (ψ t : ℝ) * (u : ℝ)
    have hψ := show (ψ s : ℝ) ≤ ψ t from hψm hst
    nlinarith [show (l : ℝ) < u from hlu]
  have hφs : Function.Surjective φ :=
    (surjective_convexComb_endpoints (l : ℝ) u hlu.le).comp hψs
  let xu := ContinuousBVPaths.restrict x l u hlu.le
  obtain ⟨y, hy, hyarea⟩ := curveArea_comp_monotone_surjective
    hlu.le v.property.2 xu φ hφc hφm hφs
  have hyval : y.val = (ContinuousBVPaths.restrict r v ⟨2, by norm_num⟩
      v.property.2).val := by
    rw [hy]
    funext w
    simp only [xu, ContinuousBVPaths.restrict, Function.comp_apply]
    rw [hr]
    have hwlow : 1 + (θ : ℝ) ≤ (w : ℝ) := w.property.1
    have hwsub : (w : ℝ) - 1 ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · linarith
      · linarith [w.property.2]
    have hwnle : ¬(w : ℝ) ≤ 1 := by
      linarith
    simp only [Function.concatUnitIntervals, hwnle, ↓reduceIte,
      Set.projIcc_of_mem (by norm_num) hwsub]
    apply congrArg x.val
    apply Subtype.ext
    have hθval := congrArg Subtype.val hθ
    change (1 - (θ : ℝ)) * a + (θ : ℝ) * u = (l : ℝ) at hθval
    dsimp only [φ, ψ]
    simp only [Set.Icc.coe_convexComb]
    dsimp only [v]
    rw [← hθval]
    have hdenne : 2 - (1 + (θ : ℝ)) ≠ 0 := by linarith
    field_simp [hdenne]
    ring
  have hyEq : y = ContinuousBVPaths.restrict r v ⟨2, by norm_num⟩ v.property.2 := by
    ext w i
    exact congrArg (fun z : Point ↦ z i) (congrFun hyval w)
  rw [← hyEq, hyarea]

private theorem exists_complementary_rectifiableOrientedArc_with_area
    {a b : ℝ} {x : ContinuousBVPaths a b} {Γ : Set Point}
    (hab : a ≤ b) (hx : IsOrientedJordanParametrization hab Γ true x.val)
    (l u : Set.Icc a b) (hal : a < l) (hlu : l < u) (hub : (u : ℝ) < b)
    (P Q : Point) (hlQ : x.val l = Q) (huP : x.val u = P) :
    ∃ A : RectifiableOrientedArc,
      A.val.carrier = Set.range x.val \ x.val '' {z | l < z ∧ z < u} ∧
      A.val.startPoint = P ∧ A.val.endPoint = Q ∧
      curveAreaFunctional x = jordanArcArea A +
        curveAreaFunctional (ContinuousBVPaths.restrict x l u hlu.le) := by
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
  obtain ⟨A, hAcarrier, hAstart, hAend, hAarea⟩ :=
    exists_rectifiableOrientedArc_restrict_closedJordan_with_area
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
  have hcarrier : A.val.carrier =
      Set.range x.val \ x.val '' {z | l < z ∧ z < u} := by
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
  have hsuffix : curveAreaFunctional
      (ContinuousBVPaths.restrict r v ⟨2, by norm_num⟩ v.property.2) =
      curveAreaFunctional (ContinuousBVPaths.restrict x l u hlu.le) :=
    curveArea_cyclicSuffix_eq_restriction hab x l u hal hlu θ hθ r hr
  obtain ⟨r', hr', _, hrotate'⟩ :=
    exists_cyclic_rotation_eq_concat hab x u hx.2.2.2.2.1.symm
  have hrr : r = r' := by
    ext w i
    exact congrArg (fun z : Point ↦ z i) (congrFun (hr.trans hr'.symm) w)
  have hrotate : curveAreaFunctional r = curveAreaFunctional x := by
    rw [hrr]
    exact hrotate'
  have hsplit := curveArea_eq_restriction_add_restriction (by norm_num) r v
  dsimp only at hsplit
  refine ⟨A, hcarrier, hAstart.trans hrzero, hAend.trans hrv, ?_⟩
  rw [← hrotate, hsplit, ← hAarea, hsuffix]

private theorem exists_rectifiableOrientedArc_of_cut_parametrization_with_area
    {a b : ℝ} {x : ContinuousBVPaths a b} {Γ U : Set Point}
    (hab : a ≤ b) (hx : IsOrientedJordanParametrization hab Γ true x.val)
    (l u : Set.Icc a b) (hal : a < l) (hlu : l < u) (hub : (u : ℝ) < b)
    (P Q : Point) (hl : x.val l = Q) (hu : x.val u = P)
    (hfrontier : Γ = U ∪ segment ℝ P Q)
    (hinter : U ∩ segment ℝ P Q = {P, Q})
    (himage : x.val '' Set.Icc l u = segment ℝ P Q) :
    ∃ A : RectifiableOrientedArc,
      A.val.carrier = U ∧ A.val.startPoint = P ∧ A.val.endPoint = Q ∧
      curveAreaFunctional x = jordanArcArea A +
        curveAreaFunctional (ContinuousBVPaths.restrict x l u hlu.le) := by
  obtain ⟨A, hA, hstart, hend, harea⟩ :=
    exists_complementary_rectifiableOrientedArc_with_area
      hab hx l u hal hlu hub P Q hl hu
  refine ⟨A, ?_, hstart, hend, harea⟩
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

theorem endpoints_eq_of_counterclockwise_supporting_chord
    {a b : ℝ} {x : ContinuousBVPaths a b} {Γ : Set Point}
    (hab : a < b) (hx : IsOrientedJordanParametrization hab.le Γ true x.val)
    (l u : Set.Icc a b) (hlu : l < u) (hub : (u : ℝ) < b)
    (P Q : Point) (hPQ : P ≠ Q)
    (himage : x.val '' Set.Icc l u = segment ℝ P Q)
    (θ : Real.Angle) (h : ℝ)
    (hhalf : Γ ⊆ normalHalfPlane θ h false false)
    (hQline : Q ∈ normalLine θ h) (d : ℝ) (hd : 0 < d)
    (hdir : P = Q + d • tangentVector θ) :
    x.val l = Q ∧ x.val u = P := by
  rcases endpoints_eq_or_eq_swap_of_image_Icc_eq_segment hab.le
      hx.2.2.2.2.2.1 l u hlu hub P Q hPQ himage with hbad | hgood
  · exfalso
    let r := Set.Icc.reverse hab.le
    let y : Set.Icc a b → Point := x.val ∘ r
    let l' := r u
    let u' := r l
    have hl'u' : l' < u' := by
      have hlu' : (l : ℝ) < u := hlu
      change a + b - (u : ℝ) < a + b - (l : ℝ)
      linarith
    have hyrange : Set.range y = Γ := by
      rw [show Set.range y = Set.range x.val by
        apply Set.Subset.antisymm
        · rintro z ⟨s, rfl⟩; exact ⟨r s, rfl⟩
        · rintro z ⟨s, rfl⟩
          obtain ⟨q, hq⟩ := Set.Icc.surjective_reverse hab.le s
          exact ⟨q, by simpa [y, r] using congrArg x.val hq⟩]
      exact hx.2.2.2.1
    have hyl : y l' = Q := by
      change x.val (r (r u)) = Q
      rw [show r (r u) = u by exact Set.Icc.involutive_reverse hab.le u, hbad.2]
    have hyu : y u' = P := by
      change x.val (r (r l)) = P
      rw [show r (r l) = l by exact Set.Icc.involutive_reverse hab.le l, hbad.1]
    have hytrue := jordan_counterclockwise_of_supporting_segment a b hab y
      (hx.2.2.1.comp (Set.Icc.continuous_reverse hab.le))
      (by rw [hyrange]; exact hx.2.1)
      (by simpa [y, r, Set.Icc.reverse] using hx.2.2.2.2.1.symm)
      (injOn_comp_reverse_of_closed_injOn hab x.val hx.2.2.2.2.1
        hx.2.2.2.2.2.1) θ h
      (fun z ↦ hhalf (by rw [← hyrange]; exact Set.mem_range_self z)) l' u' hl'u'
      (by rw [hyl]; exact hQline) d hd
      (by rw [hyl, hyu, hdir])
      (by rw [image_Icc_reverse_interval hab.le x.val l u hlu.le, himage,
        segment_symm ℝ P Q, hyl, hyu])
    rw [hyrange] at hytrue
    have horient := hx.orientation_eq_not_of_comp hytrue r
      (Set.Icc.continuous_reverse hab.le) (by simp [r, Set.Icc.reverse])
      (by simp [r, Set.Icc.reverse]) rfl
    norm_num at horient
  · exact hgood

/-- Removing a supporting chord from a counterclockwise closed BV Jordan path gives the
complementary arc, and closed signed area splits into arc area and the oriented chord area. -/
theorem exists_rectifiableOrientedArc_of_supportingChord_with_area
    {a b : ℝ} {x : ContinuousBVPaths a b} {Γ U : Set Point}
    (hab : a < b) (hx : IsOrientedJordanParametrization hab.le Γ true x.val)
    (P Q : Point) (hPQ : P ≠ Q)
    (hbase : x.val ⟨a, le_rfl, hab.le⟩ ∉ segment ℝ P Q)
    (hfrontier : Γ = U ∪ segment ℝ P Q)
    (hinter : U ∩ segment ℝ P Q = {P, Q})
    (θ : Real.Angle) (h : ℝ)
    (hhalf : Γ ⊆ normalHalfPlane θ h false false)
    (hQline : Q ∈ normalLine θ h) (d : ℝ) (hd : 0 < d)
    (hdir : P = Q + d • tangentVector θ) :
    ∃ A : RectifiableOrientedArc,
      A.val.carrier = U ∧ A.val.startPoint = P ∧ A.val.endPoint = Q ∧
      curveAreaFunctional x = jordanArcArea A + segmentArea Q P := by
  have hsegment : segment ℝ P Q ⊆ Γ := by
    rw [hfrontier]
    exact Set.subset_union_right
  obtain ⟨l, u, hal, hlu, hub, himage⟩ :=
    exists_parameter_interval_of_segment_subset_closedJordan
      hab hx P Q hPQ hsegment hbase
  have hend := endpoints_eq_of_counterclockwise_supporting_chord hab hx l u hlu hub
    P Q hPQ himage θ h hhalf hQline d hd hdir
  obtain ⟨A, hA, hAstart, hAend, harea⟩ :=
    exists_rectifiableOrientedArc_of_cut_parametrization_with_area hab.le hx l u hal hlu hub
      P Q hend.1 hend.2 hfrontier hinter himage
  obtain ⟨B, hBcarrier, hBstart, hBend, hBarea⟩ :=
    exists_rectifiableOrientedArc_restrict_closedJordan_with_area
      hab.le hx l u hlu.le hub
  obtain ⟨S, hScarrier, hSstart, hSend, hSarea⟩ :=
    (segmentArea_jordan_and_frame Q P).1
  have hBcarrier' : B.val.carrier = segment ℝ Q P := by
    rw [hBcarrier]
    change Set.range (x.val ∘ fun z : Set.Icc (l : ℝ) u ↦
      (⟨z, le_trans l.property.1 z.property.1,
        le_trans z.property.2 u.property.2⟩ : Set.Icc a b)) = _
    rw [segment_symm ℝ Q P, ← himage]
    ext p
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨⟨z, le_trans l.property.1 z.property.1,
        le_trans z.property.2 u.property.2⟩, z.property, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩
  have hBstart' : B.val.startPoint = Q := hBstart.trans hend.1
  have hBend' : B.val.endPoint = P := hBend.trans hend.2
  have hBSarea : jordanArcArea B = jordanArcArea S := by
    change curveAreaFunctional (Classical.choice B.property).path =
      curveAreaFunctional (Classical.choice S.property).path
    exact (curveArea_reparametrization.2.1 B.val S.val
      (Classical.choice B.property) (Classical.choice S.property)
      (hBcarrier'.trans hScarrier.symm)).1
        (hBstart'.trans hSstart.symm) (hBend'.trans hSend.symm)
  refine ⟨A, hA, hAstart, hAend, ?_⟩
  rw [harea, ← hBarea, hBSarea, hSarea]

end MovingSofa
