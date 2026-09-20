import MovingSofa.Curve.Jordan.Area
import MovingSofa.ForMathlib.Topology.Order.IntervalExtension
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.IntermediateValue

noncomputable section

open Set Function

namespace MovingSofa

private def openIntervalToIntervalInterior {a b : ℝ} (_hab : a < b) :
    Set.Ioo a b ≃ₜ {t : Set.Icc a b | a < (t : ℝ) ∧ (t : ℝ) < b} where
  toFun t := ⟨⟨t, t.property.1.le, t.property.2.le⟩, t.property⟩
  invFun t := ⟨t, t.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_subtype_val.subtype_mk fun t ↦ ⟨t.property.1.le, t.property.2.le⟩).subtype_mk _
  continuous_invFun := continuous_subtype_val.comp continuous_subtype_val |>.subtype_mk _

private def intervalToRange {a b : ℝ} (x : Set.Icc a b → Point) :
    Set.Icc a b → Set.range x := fun t ↦ ⟨x t, ⟨t, rfl⟩⟩

private theorem intervalToRange_continuous {a b : ℝ} (x : Set.Icc a b → Point)
    (hx : Continuous x) : Continuous (intervalToRange x) :=
  hx.subtype_mk fun t ↦ ⟨t, rfl⟩

private theorem intervalToRange_surjective {a b : ℝ} (x : Set.Icc a b → Point) :
    Function.Surjective (intervalToRange x) := by
  rintro ⟨p, t, rfl⟩
  exact ⟨t, rfl⟩

/-- The carrier of a closed parametrized loop with its basepoint removed. -/
def puncturedLoopRangeSet {a b : ℝ} (hab : a ≤ b)
    (x : Set.Icc a b → Point) : Set (Set.range x) :=
  {p | (p : Point) ≠ x ⟨a, le_rfl, hab⟩}

private theorem puncturedLoopRangeSet_isOpen {a b : ℝ} (hab : a ≤ b)
    (x : Set.Icc a b → Point) : IsOpen (puncturedLoopRangeSet hab x) := by
  let p : Set.range x := ⟨x ⟨a, le_rfl, hab⟩, ⟨⟨a, le_rfl, hab⟩, rfl⟩⟩
  rw [show puncturedLoopRangeSet hab x = ({p}ᶜ : Set (Set.range x)) by
    ext q
    change ((q : Point) ≠ (p : Point)) ↔ q ≠ p
    exact not_congr Subtype.ext_iff.symm]
  exact isOpen_compl_singleton

private theorem intervalToRange_preimage_punctured {a b : ℝ} (hab : a ≤ b)
    (hab' : a < b) (x : Set.Icc a b → Point)
    (hclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    (hinj : Set.InjOn x {t | (t : ℝ) < b}) :
    intervalToRange x ⁻¹' puncturedLoopRangeSet hab x =
      {t : Set.Icc a b | a < (t : ℝ) ∧ (t : ℝ) < b} := by
  ext t
  simp only [Set.mem_preimage, puncturedLoopRangeSet, Set.mem_ofPred_eq, intervalToRange]
  constructor
  · intro ht
    constructor
    · exact lt_of_le_of_ne t.property.1 fun hta ↦ by
        apply ht
        exact congrArg x (Subtype.ext hta.symm)
    · exact lt_of_le_of_ne t.property.2 fun htb ↦ by
        apply ht
        have ht_top : t = ⟨b, hab, le_rfl⟩ := Subtype.ext htb
        rw [ht_top]
        exact hclosed.symm
  · rintro ⟨hat, htb⟩ htx
    have : t = ⟨a, le_rfl, hab⟩ := hinj htb hab' htx
    exact hat.ne (congrArg Subtype.val this).symm

private theorem intervalToPuncturedRange_injective {a b : ℝ} (hab : a ≤ b)
    (_hab' : a < b) (x : Set.Icc a b → Point)
    (hclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    (hinj : Set.InjOn x {t | (t : ℝ) < b}) :
    Function.Injective
      ((puncturedLoopRangeSet hab x).restrictPreimage (intervalToRange x)) := by
  intro s t hst
  apply Subtype.ext
  apply hinj (x₁ := s.val) (x₂ := t.val)
  · have hsne : x s.val ≠ x ⟨a, le_rfl, hab⟩ := s.property
    exact lt_of_le_of_ne s.val.property.2 fun hsb ↦ by
      apply hsne
      have hs_top : s.val = ⟨b, hab, le_rfl⟩ := Subtype.ext hsb
      rw [hs_top]
      exact hclosed.symm
  · have htne : x t.val ≠ x ⟨a, le_rfl, hab⟩ := t.property
    exact lt_of_le_of_ne t.val.property.2 fun htb ↦ by
      apply htne
      have ht_top : t.val = ⟨b, hab, le_rfl⟩ := Subtype.ext htb
      rw [ht_top]
      exact hclosed.symm
  · exact congrArg (fun p : puncturedLoopRangeSet hab x ↦ (p : Point)) hst

/-- Removing the basepoint turns a closed once-traversal into a homeomorphism from the
open parameter interval onto the punctured carrier. -/
noncomputable def openIntervalHomeomorphPuncturedRange {a b : ℝ} (hab : a ≤ b)
    (hab' : a < b) (x : Set.Icc a b → Point) (hx : Continuous x)
    (hclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    (hinj : Set.InjOn x {t | (t : ℝ) < b}) :
    Set.Ioo a b ≃ₜ puncturedLoopRangeSet hab x := by
  let f := intervalToRange x
  let s := puncturedLoopRangeSet hab x
  have hfq : Topology.IsQuotientMap f :=
    (intervalToRange_continuous x hx).isClosedMap.isQuotientMap
      (intervalToRange_continuous x hx) (intervalToRange_surjective x)
  have hgq : Topology.IsQuotientMap (s.restrictPreimage f) :=
    hfq.restrictPreimage_isOpen (puncturedLoopRangeSet_isOpen hab x)
  have hgh : IsHomeomorph (s.restrictPreimage f) :=
    isHomeomorph_iff_isQuotientMap_injective.2
      ⟨hgq, intervalToPuncturedRange_injective hab hab' x hclosed hinj⟩
  exact (openIntervalToIntervalInterior hab').trans <|
    (Homeomorph.setCongr
      (intervalToRange_preimage_punctured hab hab' x hclosed hinj).symm).trans
      (hgh.homeomorph _)

/-- The punctured-loop homeomorphism agrees pointwise with the original path. -/
theorem openIntervalHomeomorphPuncturedRange_coe {a b : ℝ} (hab : a ≤ b)
    (hab' : a < b) (x : Set.Icc a b → Point) (hx : Continuous x)
    (hclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    (hinj : Set.InjOn x {t | (t : ℝ) < b}) (t : Set.Ioo a b) :
    ((openIntervalHomeomorphPuncturedRange hab hab' x hx hclosed hinj t :
        puncturedLoopRangeSet hab x) : Point) =
      x ⟨t, t.property.1.le, t.property.2.le⟩ := by
  rfl

private def puncturedLoopRangeHomeomorphOfEq
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (x : Set.Icc a b → Point) (y : Set.Icc c d → Point)
    (hrange : Set.range x = Set.range y)
    (hstart : x ⟨a, le_rfl, hab⟩ = y ⟨c, le_rfl, hcd⟩) :
    puncturedLoopRangeSet hcd y ≃ₜ puncturedLoopRangeSet hab x where
  toFun q :=
    ⟨⟨q, by rw [hrange]; exact q.val.property⟩, fun h ↦ q.property (h.trans hstart)⟩
  invFun q :=
    ⟨⟨q, by rw [← hrange]; exact q.val.property⟩, fun h ↦ q.property (h.trans hstart.symm)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val |>.subtype_mk _).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.comp continuous_subtype_val |>.subtype_mk _).subtype_mk _

/-- The transition between two endpoint-matched once-traversals, restricted to their open
parameter intervals. -/
private noncomputable def openIntervalClosedCurveTransition
    {a b c d : ℝ} (hab : a ≤ b) (hab' : a < b) (hcd : c ≤ d) (hcd' : c < d)
    (x : Set.Icc a b → Point) (y : Set.Icc c d → Point)
    (hxc : Continuous x) (hyc : Continuous y)
    (hxclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    (hyclosed : y ⟨c, le_rfl, hcd⟩ = y ⟨d, hcd, le_rfl⟩)
    (hxinj : Set.InjOn x {t | (t : ℝ) < b})
    (hyinj : Set.InjOn y {t | (t : ℝ) < d})
    (hrange : Set.range x = Set.range y)
    (hstart : x ⟨a, le_rfl, hab⟩ = y ⟨c, le_rfl, hcd⟩) :
    Set.Ioo c d ≃ₜ Set.Ioo a b :=
  (openIntervalHomeomorphPuncturedRange hcd hcd' y hyc hyclosed hyinj).trans
    ((puncturedLoopRangeHomeomorphOfEq hab hcd x y hrange hstart).trans
      (openIntervalHomeomorphPuncturedRange hab hab' x hxc hxclosed hxinj).symm)

private theorem openIntervalClosedCurveTransition_point
    {a b c d : ℝ} (hab : a ≤ b) (hab' : a < b) (hcd : c ≤ d) (hcd' : c < d)
    (x : Set.Icc a b → Point) (y : Set.Icc c d → Point)
    (hxc : Continuous x) (hyc : Continuous y)
    (hxclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    (hyclosed : y ⟨c, le_rfl, hcd⟩ = y ⟨d, hcd, le_rfl⟩)
    (hxinj : Set.InjOn x {t | (t : ℝ) < b})
    (hyinj : Set.InjOn y {t | (t : ℝ) < d})
    (hrange : Set.range x = Set.range y)
    (hstart : x ⟨a, le_rfl, hab⟩ = y ⟨c, le_rfl, hcd⟩)
    (t : Set.Ioo c d) :
    x ⟨openIntervalClosedCurveTransition hab hab' hcd hcd' x y hxc hyc hxclosed
          hyclosed hxinj hyinj hrange hstart t,
        (openIntervalClosedCurveTransition hab hab' hcd hcd' x y hxc hyc hxclosed
          hyclosed hxinj hyinj hrange hstart t).property.1.le,
        (openIntervalClosedCurveTransition hab hab' hcd hcd' x y hxc hyc hxclosed
          hyclosed hxinj hyinj hrange hstart t).property.2.le⟩ =
      y ⟨t, t.property.1.le, t.property.2.le⟩ := by
  let ex := openIntervalHomeomorphPuncturedRange hab hab' x hxc hxclosed hxinj
  let ey := openIntervalHomeomorphPuncturedRange hcd hcd' y hyc hyclosed hyinj
  let ec := puncturedLoopRangeHomeomorphOfEq hab hcd x y hrange hstart
  change x ⟨ex.symm (ec (ey t)), (ex.symm (ec (ey t))).property.1.le,
      (ex.symm (ec (ey t))).property.2.le⟩ =
    y ⟨t, t.property.1.le, t.property.2.le⟩
  rw [← openIntervalHomeomorphPuncturedRange_coe hab hab' x hxc hxclosed hxinj
      (ex.symm (ec (ey t))),
    ← openIntervalHomeomorphPuncturedRange_coe hcd hcd' y hyc hyclosed hyinj t]
  exact congrArg (fun q : puncturedLoopRangeSet hab x ↦ (q : Point))
    (ex.apply_symm_apply (ec (ey t)))

private theorem homeomorph_Ioo_strictMono_or_strictAnti
    {a b c d : ℝ} (hcd : c < d) (e : Set.Ioo c d ≃ₜ Set.Ioo a b) :
    StrictMono e ∨ StrictAnti e := by
  let f : ℝ → ℝ := Function.extend ((↑) : Set.Ioo c d → ℝ)
    (fun t ↦ (e t : ℝ)) 0
  have hf_apply (t : Set.Ioo c d) : f t = (e t : ℝ) :=
    Subtype.val_injective.extend_apply _ _ t
  have hfc : ContinuousOn f (Set.Ioo c d) := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert continuous_subtype_val.comp e.continuous using 1
    funext t
    exact hf_apply t
  have hfi : Set.InjOn f (Set.Ioo c d) := by
    intro s hs t ht hst
    have heq : e ⟨s, hs⟩ = e ⟨t, ht⟩ := by
      apply Subtype.ext
      calc
        (e ⟨s, hs⟩ : ℝ) = f s := (hf_apply ⟨s, hs⟩).symm
        _ = f t := hst
        _ = (e ⟨t, ht⟩ : ℝ) := hf_apply ⟨t, ht⟩
    exact congrArg Subtype.val (e.injective heq)
  rcases ContinuousOn.strictMonoOn_of_injOn_Ioo hcd hfc hfi with hm | ha
  · left
    intro s t hst
    have := hm s.property t.property hst
    change (e s : ℝ) < (e t : ℝ)
    simpa only [hf_apply] using this
  · right
    intro s t hst
    have := ha s.property t.property hst
    change (e t : ℝ) < (e s : ℝ)
    simpa only [hf_apply] using this

private def closedIntervalReverse {a b : ℝ} (_hab : a ≤ b) :
    Set.Icc a b ≃ₜ Set.Icc a b where
  toFun t := ⟨a + b - t, by linarith [t.property.2], by linarith [t.property.1]⟩
  invFun t := ⟨a + b - t, by linarith [t.property.2], by linarith [t.property.1]⟩
  left_inv t := by apply Subtype.ext; dsimp; ring
  right_inv t := by apply Subtype.ext; dsimp; ring
  continuous_toFun :=
    (continuous_const.add continuous_const |>.sub continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (continuous_const.add continuous_const |>.sub continuous_subtype_val).subtype_mk _

private theorem closedIntervalReverse_antitone {a b : ℝ} (_hab : a ≤ b) :
    Antitone (closedIntervalReverse _hab) := by
  intro s t hst
  have hst' : (s : ℝ) ≤ (t : ℝ) := hst
  change a + b - (t : ℝ) ≤ a + b - (s : ℝ)
  linarith

private theorem closedIntervalReverse_left {a b : ℝ} (hab : a ≤ b) :
    closedIntervalReverse hab ⟨a, le_rfl, hab⟩ = ⟨b, hab, le_rfl⟩ := by
  apply Subtype.ext
  dsimp [closedIntervalReverse]
  ring

private theorem closedIntervalReverse_right {a b : ℝ} (hab : a ≤ b) :
    closedIntervalReverse hab ⟨b, hab, le_rfl⟩ = ⟨a, le_rfl, hab⟩ := by
  apply Subtype.ext
  dsimp [closedIntervalReverse]
  ring

private def openIntervalReverse {a b : ℝ} (_hab : a < b) :
    Set.Ioo a b ≃ₜ Set.Ioo a b where
  toFun t := ⟨a + b - t, by linarith [t.property.2], by linarith [t.property.1]⟩
  invFun t := ⟨a + b - t, by linarith [t.property.2], by linarith [t.property.1]⟩
  left_inv t := by apply Subtype.ext; dsimp; ring
  right_inv t := by apply Subtype.ext; dsimp; ring
  continuous_toFun :=
    (continuous_const.add continuous_const |>.sub continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (continuous_const.add continuous_const |>.sub continuous_subtype_val).subtype_mk _

private theorem openIntervalReverse_strictAnti {a b : ℝ} (_hab : a < b) :
    StrictAnti (openIntervalReverse _hab) := by
  intro s t hst
  have hst' : (s : ℝ) < (t : ℝ) := hst
  change a + b - (t : ℝ) < a + b - (s : ℝ)
  linarith

private theorem openIntervalClosedCurveTransition_strictMono_or_strictAnti
    {a b c d : ℝ} (hab : a ≤ b) (hab' : a < b) (hcd : c ≤ d) (hcd' : c < d)
    (x : Set.Icc a b → Point) (y : Set.Icc c d → Point)
    (hxc : Continuous x) (hyc : Continuous y)
    (hxclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    (hyclosed : y ⟨c, le_rfl, hcd⟩ = y ⟨d, hcd, le_rfl⟩)
    (hxinj : Set.InjOn x {t | (t : ℝ) < b})
    (hyinj : Set.InjOn y {t | (t : ℝ) < d})
    (hrange : Set.range x = Set.range y)
    (hstart : x ⟨a, le_rfl, hab⟩ = y ⟨c, le_rfl, hcd⟩) :
    StrictMono (openIntervalClosedCurveTransition hab hab' hcd hcd' x y hxc hyc
      hxclosed hyclosed hxinj hyinj hrange hstart) ∨
    StrictAnti (openIntervalClosedCurveTransition hab hab' hcd hcd' x y hxc hyc
      hxclosed hyclosed hxinj hyinj hrange hstart) :=
  homeomorph_Ioo_strictMono_or_strictAnti hcd'
    (openIntervalClosedCurveTransition hab hab' hcd hcd' x y hxc hyc hxclosed
      hyclosed hxinj hyinj hrange hstart)

/-- An endpoint-matched pair of continuous once-traversals of the same carrier differ by a
continuous surjective monotone or antitone reparametrization of the closed intervals. -/
private theorem exists_reparametrization_with_endpoints
    {a b c d : ℝ} (hab : a ≤ b) (hab' : a < b) (hcd : c ≤ d) (hcd' : c < d)
    (x : Set.Icc a b → Point) (y : Set.Icc c d → Point)
    (hxc : Continuous x) (hyc : Continuous y)
    (hxclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    (hyclosed : y ⟨c, le_rfl, hcd⟩ = y ⟨d, hcd, le_rfl⟩)
    (hxinj : Set.InjOn x {t | (t : ℝ) < b})
    (hyinj : Set.InjOn y {t | (t : ℝ) < d})
    (hrange : Set.range x = Set.range y)
    (hstart : x ⟨a, le_rfl, hab⟩ = y ⟨c, le_rfl, hcd⟩) :
    ∃ φ : Set.Icc c d → Set.Icc a b,
      Continuous φ ∧ Function.Surjective φ ∧
      ((Monotone φ ∧ φ ⟨c, le_rfl, hcd⟩ = ⟨a, le_rfl, hab⟩ ∧
          φ ⟨d, hcd, le_rfl⟩ = ⟨b, hab, le_rfl⟩) ∨
        (Antitone φ ∧ φ ⟨c, le_rfl, hcd⟩ = ⟨b, hab, le_rfl⟩ ∧
          φ ⟨d, hcd, le_rfl⟩ = ⟨a, le_rfl, hab⟩)) ∧
      ∀ t, x (φ t) = y t := by
  let e := openIntervalClosedCurveTransition hab hab' hcd hcd' x y hxc hyc
    hxclosed hyclosed hxinj hyinj hrange hstart
  rcases openIntervalClosedCurveTransition_strictMono_or_strictAnti hab hab' hcd hcd'
      x y hxc hyc hxclosed hyclosed hxinj hyinj hrange hstart with hm | ha
  · let eo : Set.Ioo c d ≃o Set.Ioo a b :=
      StrictMono.orderIsoOfRightInverse e hm e.symm e.apply_symm_apply
    let φ := OrderIso.extendIoo hab' eo
    refine ⟨φ, OrderIso.continuous_extendIoo hcd' hab' eo,
      OrderIso.surjective_extendIoo hcd' hab' eo, Or.inl ⟨?_, ?_, ?_⟩, ?_⟩
    · exact OrderIso.monotone_extendIoo hcd' hab' eo
    · exact OrderIso.extendIoo_left hcd' hab' eo
    · exact OrderIso.extendIoo_right hcd' hab' eo
    · intro t
      by_cases htc : (t : ℝ) = c
      · have ht : t = ⟨c, le_rfl, hcd⟩ := Subtype.ext htc
        rw [ht, show φ ⟨c, le_rfl, hcd⟩ = ⟨a, le_rfl, hab⟩ from
          OrderIso.extendIoo_left hcd' hab' eo]
        exact hstart
      by_cases htd : (t : ℝ) = d
      · have ht : t = ⟨d, hcd, le_rfl⟩ := Subtype.ext htd
        rw [ht, show φ ⟨d, hcd, le_rfl⟩ = ⟨b, hab, le_rfl⟩ from
          OrderIso.extendIoo_right hcd' hab' eo]
        exact hxclosed.symm.trans (hstart.trans hyclosed)
      · let ti : Set.Ioo c d :=
          ⟨t, lt_of_le_of_ne t.property.1 (Ne.symm htc),
            lt_of_le_of_ne t.property.2 htd⟩
        have hφ : φ t = ⟨e ti, (e ti).property.1.le, (e ti).property.2.le⟩ := by
          apply Subtype.ext
          have ht : t = ⟨ti, ti.property.1.le, ti.property.2.le⟩ := Subtype.ext rfl
          rw [ht]
          exact OrderIso.extendIoo_interior hab' eo ti
        rw [hφ]
        exact openIntervalClosedCurveTransition_point hab hab' hcd hcd' x y hxc hyc
          hxclosed hyclosed hxinj hyinj hrange hstart ti
  · let r := openIntervalReverse hab'
    let g : Set.Ioo c d ≃ₜ Set.Ioo a b := e.trans r
    have hgm : StrictMono g := by
      intro s t hst
      exact openIntervalReverse_strictAnti hab' (ha hst)
    let go : Set.Ioo c d ≃o Set.Ioo a b :=
      StrictMono.orderIsoOfRightInverse g hgm g.symm g.apply_symm_apply
    let ψ := OrderIso.extendIoo hab' go
    let φ : Set.Icc c d → Set.Icc a b := fun t ↦ closedIntervalReverse hab (ψ t)
    refine ⟨φ, (closedIntervalReverse hab).continuous.comp
        (OrderIso.continuous_extendIoo hcd' hab' go),
      (closedIntervalReverse hab).surjective.comp
        (OrderIso.surjective_extendIoo hcd' hab' go), Or.inr ⟨?_, ?_, ?_⟩, ?_⟩
    · exact (closedIntervalReverse_antitone hab).comp_monotone
        (OrderIso.monotone_extendIoo hcd' hab' go)
    · rw [show φ ⟨c, le_rfl, hcd⟩ =
          closedIntervalReverse hab (ψ ⟨c, le_rfl, hcd⟩) from rfl,
        show ψ ⟨c, le_rfl, hcd⟩ = ⟨a, le_rfl, hab⟩ from
          OrderIso.extendIoo_left hcd' hab' go]
      apply Subtype.ext
      dsimp [closedIntervalReverse]
      ring
    · rw [show φ ⟨d, hcd, le_rfl⟩ =
          closedIntervalReverse hab (ψ ⟨d, hcd, le_rfl⟩) from rfl,
        show ψ ⟨d, hcd, le_rfl⟩ = ⟨b, hab, le_rfl⟩ from
          OrderIso.extendIoo_right hcd' hab' go]
      apply Subtype.ext
      dsimp [closedIntervalReverse]
      ring
    · intro t
      by_cases htc : (t : ℝ) = c
      · have ht : t = ⟨c, le_rfl, hcd⟩ := Subtype.ext htc
        rw [ht]
        change x (closedIntervalReverse hab (ψ ⟨c, le_rfl, hcd⟩)) = _
        rw [show ψ ⟨c, le_rfl, hcd⟩ = ⟨a, le_rfl, hab⟩ from
          OrderIso.extendIoo_left hcd' hab' go]
        rw [closedIntervalReverse_left hab]
        exact hxclosed.symm.trans hstart
      by_cases htd : (t : ℝ) = d
      · have ht : t = ⟨d, hcd, le_rfl⟩ := Subtype.ext htd
        rw [ht]
        change x (closedIntervalReverse hab (ψ ⟨d, hcd, le_rfl⟩)) = _
        rw [show ψ ⟨d, hcd, le_rfl⟩ = ⟨b, hab, le_rfl⟩ from
          OrderIso.extendIoo_right hcd' hab' go]
        rw [closedIntervalReverse_right hab]
        exact hstart.trans hyclosed
      · let ti : Set.Ioo c d :=
          ⟨t, lt_of_le_of_ne t.property.1 (Ne.symm htc),
            lt_of_le_of_ne t.property.2 htd⟩
        have hφ : φ t = ⟨e ti, (e ti).property.1.le, (e ti).property.2.le⟩ := by
          apply Subtype.ext
          have hψ := OrderIso.extendIoo_interior hab' go ti
          dsimp [go, g, r] at hψ
          change a + b - (ψ t : ℝ) = (e ti : ℝ)
          rw [hψ]
          change a + b - (a + b - (e ti : ℝ)) = (e ti : ℝ)
          ring
        rw [hφ]
        exact openIntervalClosedCurveTransition_point hab hab' hcd hcd' x y hxc hyc
          hxclosed hyclosed hxinj hyinj hrange hstart ti

/-- Equal-start simple closed paths with the same range admit a monotone or antitone transition. -/
theorem exists_reparametrization_of_range_eq_of_start_eq
    {a b c d : ℝ} (hab : a ≤ b) (hab' : a < b) (hcd : c ≤ d) (hcd' : c < d)
    (x : Set.Icc a b → Point) (y : Set.Icc c d → Point)
    (hxc : Continuous x) (hyc : Continuous y)
    (hxclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    (hyclosed : y ⟨c, le_rfl, hcd⟩ = y ⟨d, hcd, le_rfl⟩)
    (hxinj : Set.InjOn x {t | (t : ℝ) < b})
    (hyinj : Set.InjOn y {t | (t : ℝ) < d})
    (hrange : Set.range x = Set.range y)
    (hstart : x ⟨a, le_rfl, hab⟩ = y ⟨c, le_rfl, hcd⟩) :
    ∃ φ : Set.Icc c d → Set.Icc a b,
      Continuous φ ∧ Function.Surjective φ ∧ (Monotone φ ∨ Antitone φ) ∧
        y = x ∘ φ := by
  rcases exists_reparametrization_with_endpoints hab hab' hcd hcd' x y hxc hyc
      hxclosed hyclosed hxinj hyinj hrange hstart with ⟨φ, hφc, hφs, hφo, hφxy⟩
  refine ⟨φ, hφc, hφs, hφo.imp (fun h ↦ h.1) (fun h ↦ h.1), ?_⟩
  funext t
  exact (hφxy t).symm

/-- Equal-start closed Jordan parametrizations admit a monotone or antitone transition. -/
theorem ClosedBVParametrization.exists_reparametrization_of_start_eq
    {Γ Δ : OrientedJordanCurve} (x : ClosedBVParametrization Γ)
    (y : ClosedBVParametrization Δ) (hcarrier : Γ.carrier = Δ.carrier)
    (hstart : x.path.val ⟨x.a, le_rfl, x.ordered⟩ =
      y.path.val ⟨y.a, le_rfl, y.ordered⟩) :
    ∃ φ : Set.Icc y.a y.b → Set.Icc x.a x.b,
      Continuous φ ∧ Function.Surjective φ ∧ (Monotone φ ∨ Antitone φ) ∧
        y.path.val = x.path.val ∘ φ := by
  have hrange : Set.range x.path.val = Set.range y.path.val := by
    rw [x.oriented.2.2.2.1, y.oriented.2.2.2.1]
    exact hcarrier
  exact exists_reparametrization_of_range_eq_of_start_eq x.ordered x.oriented.1 y.ordered y.oriented.1
    x.path.val y.path.val x.path.property.1 y.path.property.1
    x.oriented.2.2.2.2.1 y.oriented.2.2.2.2.1
    x.oriented.2.2.2.2.2.1 y.oriented.2.2.2.2.2.1 hrange hstart

end MovingSofa
