import MovingSofa.Gerver.OuterContacts
import MovingSofa.Gerver.Niche.RoofProperties
import MovingSofa.Gerver.LiteralConnected
import MovingSofa.Geometry.PathHalfPlaneCap
import MovingSofa.Geometry.ContactGeometry
import MovingSofa.Geometry.HallwayPartsProperties

noncomputable section

namespace MovingSofa

theorem gerver_capSupport_identification :
    (∀ q ∈ gerverOuterCap, ∃ p ∈ gerverLiteralSofa, p 0 = q 0 ∧ q 1 ≤ p 1) ∧
    paperGerverSofa = gerverLiteralSofa ∧
    IsStandardPosition gerverLiteralSofa (Real.pi / 2) ∧
    (∀ s ∈ Set.Icc (0 : ℝ) Real.pi,
      supportValue gerverLiteralSofa (s : Real.Angle) = supportValue gerverOuterCap (s : Real.Angle)) ∧
    capOfSofa gerverLiteralSofa (Real.pi / 2) = gerverOuterCap ∧
    (∃ K : CapSpace (Real.pi / 2), (K.val : Set Point) = gerverOuterCap ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        exposedEdge K.val (t : Real.Angle) = {paperGerverContacts t 0} ∧
        exposedEdge K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) = {paperGerverContacts t 2}) ∧
      paperGerverContacts 0 0 = (edgeVertices K.val (0 : Real.Angle)).1 ∧
      paperGerverContacts (Real.pi / 2) 0 =
        (edgeVertices K.val ((Real.pi / 2 : ℝ) : Real.Angle)).2 ∧
      paperGerverContacts 0 2 = (edgeVertices K.val ((Real.pi / 2 : ℝ) : Real.Angle)).1 ∧
      paperGerverContacts (Real.pi / 2) 2 = (edgeVertices K.val (Real.pi : Real.Angle)).2) ∧
    (∀ S ∈ ({gerverOuterCap, gerverLiteralSofa} : Set (Set Point)),
      ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
        supportValue S (t : Real.Angle) =
          inner ℝ (paperGerverPath t) (normalVector (t : Real.Angle)) + 1 ∧
        supportValue S ((Real.pi / 2 + t : ℝ) : Real.Angle) =
          inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) + 1) := by
  have hTpos : (0 : ℝ) < Real.pi / 2 := by positivity
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨le_rfl, hTpos.le⟩
  have hTmem : (Real.pi / 2) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨hTpos.le, le_rfl⟩
  -- ### Path regularity and endpoints
  have hreg := gerver_direct_path_regularity GerverSofa.PartB.params
    GerverSofa.PartB.params_mem GerverSofa.PartB.params_equations
  have hC1 : ContDiff ℝ 1 (GerverSofa.Romik.path GerverSofa.PartB.params) := hreg.1
  have hpathcont : Continuous paperGerverPath := continuous_paperGerverPath hC1
  -- The clockwise motion used for the moving-sofa property, and its continuity.
  have hmotioncont : Continuous fun r : unitInterval =>
      rotateTranslate ((-(r.val * (Real.pi / 2)) : ℝ) : Real.Angle)
        (-paperGerverPath (r.val * (Real.pi / 2))) := by
    have hpair : Continuous fun r : unitInterval =>
        ((((-(r.val * (Real.pi / 2))) : ℝ) : Real.Angle),
          -paperGerverPath (r.val * (Real.pi / 2))) :=
      (Real.Angle.continuous_coe.comp (continuous_subtype_val.mul continuous_const).neg).prodMk
        ((hpathcont.comp (continuous_subtype_val.mul continuous_const)).neg)
    have heq : (fun r : unitInterval =>
          rotateTranslate ((-(r.val * (Real.pi / 2)) : ℝ) : Real.Angle)
            (-paperGerverPath (r.val * (Real.pi / 2)))) =
        (fun q : Real.Angle × Point => (AffineIsometryEquiv.vaddConst ℝ q.2).trans
          (EuclideanGeometry.o.rotation q.1).toAffineIsometryEquiv) ∘
        (fun r : unitInterval => ((((-(r.val * (Real.pi / 2))) : ℝ) : Real.Angle),
          -paperGerverPath (r.val * (Real.pi / 2)))) := rfl
    rw [heq]
    exact continuous_vaddConst_trans_rotation.comp hpair
  have hpath0 : paperGerverPath 0 = 0 := by
    show GerverSofa.PartF.Coordinates.toPlane
      (GerverSofa.Romik.path GerverSofa.PartB.params 0) = 0
    rw [hreg.2.1]
    ext i
    fin_cases i <;> rfl
  have hpathTy : paperGerverPath (Real.pi / 2) 1 = 0 :=
    GerverSofa.Romik.path_end_y_zero_of_mem_box_and_equations
      GerverSofa.PartB.params_mem GerverSofa.PartB.params_equations
  -- ### Coordinate images and compactness
  have hKimg : gerverOuterCap =
      GerverSofa.PartF.Coordinates.toPlane '' GerverSofa.Romik.K0 GerverSofa.PartB.params := by
    rw [GerverSofa.PartF.Coordinates.image_eq_preimage]
    exact Set.ext mem_gerverOuterCap_iff
  have hKcomp : IsCompact gerverOuterCap := by
    rw [hKimg]
    exact GerverSofa.PartC.Stage4.K_compact_direct.image
      GerverSofa.PartF.Coordinates.continuous_toPlane
  have hGimg : gerverLiteralSofa =
      GerverSofa.PartF.Coordinates.toPlane '' GerverSofa.PartC.G := by
    rw [GerverSofa.PartF.Coordinates.image_eq_preimage]
    exact Set.ext fun q =>
      and_congr (mem_gerverOuterCap_iff q) (not_congr (mem_gerverLiteralNiche_iff q))
  have hGcomp : IsCompact gerverLiteralSofa := by
    rw [hGimg]
    exact GerverSofa.PartC.Stage4.G_compact_direct.image
      GerverSofa.PartF.Coordinates.continuous_toPlane
  -- ### Contact coordinates in the moving frame
  have hvn : ∀ t : ℝ, inner ℝ (tangentVector (t : Real.Angle))
      (normalVector (t : Real.Angle)) = 0 := fun t => by
    rw [real_inner_comm, inner_normalVector_tangentVector]
  have hAn : ∀ t : ℝ, inner ℝ (paperGerverContacts t 0) (normalVector (t : Real.Angle)) =
      inner ℝ (paperGerverPath t) (normalVector (t : Real.Angle)) + 1 := fun t => by
    simp only [paperGerverContacts, Matrix.cons_val_zero, inner_add_left, real_inner_smul_left,
      inner_normalVector_self, hvn t]
    ring
  have hAt : ∀ t : ℝ, inner ℝ (paperGerverContacts t 0) (tangentVector (t : Real.Angle)) =
      inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) +
        (paperGerverVelocityComponents t).1 := fun t => by
    simp only [paperGerverContacts, Matrix.cons_val_zero, inner_add_left, real_inner_smul_left,
      inner_tangentVector_self, inner_normalVector_tangentVector]
    ring
  have hCn : ∀ t : ℝ, inner ℝ (paperGerverContacts t 2) (normalVector (t : Real.Angle)) =
      inner ℝ (paperGerverPath t) (normalVector (t : Real.Angle)) -
        (paperGerverVelocityComponents t).2 := fun t => by
    simp only [paperGerverContacts, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
      inner_add_left, inner_sub_left, real_inner_smul_left, inner_normalVector_self, hvn t]
    ring
  have hCt : ∀ t : ℝ, inner ℝ (paperGerverContacts t 2) (tangentVector (t : Real.Angle)) =
      inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) + 1 := fun t => by
    simp only [paperGerverContacts, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
      inner_add_left, inner_sub_left, real_inner_smul_left, inner_tangentVector_self,
      inner_normalVector_tangentVector]
    ring
  -- ### The cap is the outer path constraint set
  have hOPCS : outerPathConstraintSet
      (fun t : Set.Icc (0 : ℝ) (Real.pi / 2) => paperGerverPath t.val) = gerverOuterCap := by
    ext q
    constructor
    · rintro ⟨hy, h⟩
      exact ⟨hy, fun t ht => h ⟨t, ht⟩⟩
    · rintro ⟨hy, h⟩
      exact ⟨hy, fun t => h t.val t.2⟩
  -- ### The two normalizing contacts
  have halpha0 : (paperGerverVelocityComponents 0).1 = 0 := by
    rw [paperGerverVelocityComponents_eq_alphaBetaAt 0 h0mem]
    have hab : GerverSofa.PartC.alphaBetaAt 0 =
        GerverSofa.Romik.alphaBeta1 GerverSofa.PartB.params 0 := by
      rw [GerverSofa.PartC.alphaBetaAt]
      simp [GerverSofa.PartC.Stage4.phi_pos.le]
    have ha2 := GerverSofa.Romik.a2_eq_neg_quarter_of_equations GerverSofa.PartB.params_equations
    rw [hab]
    simp only [GerverSofa.Romik.alphaBeta1, Real.sin_zero, Real.cos_zero, ha2]
    ring
  have hA0y : paperGerverContacts 0 0 1 = 0 := by
    have h := inner_tangentVector_zero (paperGerverContacts 0 0)
    rw [hAt 0, hpath0, inner_zero_left, halpha0] at h
    linarith
  have hC0y : paperGerverContacts 0 2 1 = 1 := by
    have h := inner_tangentVector_zero (paperGerverContacts 0 2)
    rw [hCt 0, hpath0, inner_zero_left] at h
    linarith
  obtain ⟨Kb, hKset, hKcap⟩ := outerPathConstraintSet_isCap
    (fun t : Set.Icc (0 : ℝ) (Real.pi / 2) => paperGerverPath t.val)
    (by simpa using hpath0)
    ⟨paperGerverContacts 0 0, by rw [hOPCS]; exact gerver_outer_contact_A 0 h0mem, hA0y⟩
    ⟨paperGerverContacts 0 2, by rw [hOPCS]; exact gerver_outer_contact_C 0 h0mem, hC0y⟩
  rw [hOPCS] at hKset
  -- ### Conjunct 1: every cap fibre has a sofa point at least as high
  have hfiber : ∀ q ∈ gerverOuterCap,
      ∃ p ∈ gerverLiteralSofa, p 0 = q 0 ∧ q 1 ≤ p 1 := by
    intro q hq
    have hFcomp : IsCompact (gerverOuterCap ∩ {z : Point |
        inner ℝ z (normalVector ((0 : ℝ) : Real.Angle)) =
          inner ℝ q (normalVector ((0 : ℝ) : Real.Angle))}) :=
      hKcomp.inter_right (isClosed_eq (continuous_id.inner continuous_const) continuous_const)
    obtain ⟨p, hpF, hpmax⟩ := hFcomp.exists_isMaxOn ⟨q, hq, rfl⟩
      (f := fun z : Point => inner ℝ z (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)))
      (continuous_id.inner continuous_const).continuousOn
    have hpx : p 0 = q 0 := by
      have h : inner ℝ p (normalVector ((0 : ℝ) : Real.Angle)) =
        inner ℝ q (normalVector ((0 : ℝ) : Real.Angle)) := hpF.2
      rwa [inner_normalVector_zero, inner_normalVector_zero] at h
    have hpy : q 1 ≤ p 1 := by
      have h : inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) ≤
        inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) := hpmax ⟨hq, rfl⟩
      rwa [inner_normalVector_pi_div_two, inner_normalVector_pi_div_two] at h
    have hnofill : ∀ (f : ℝ → Point) (I : Set ℝ), (∀ t ∈ I, f t ∈ gerverOuterCap) →
        p ∉ strictVerticalFill f I := by
      rintro f I hf ⟨t, ht, h0, -, h2⟩
      have hmem : f t ∈ gerverOuterCap ∩ {z : Point |
          inner ℝ z (normalVector ((0 : ℝ) : Real.Angle)) =
            inner ℝ q (normalVector ((0 : ℝ) : Real.Angle))} := by
        refine ⟨hf t ht, ?_⟩
        show inner ℝ (f t) (normalVector ((0 : ℝ) : Real.Angle)) =
          inner ℝ q (normalVector ((0 : ℝ) : Real.Angle))
        rw [inner_normalVector_zero, inner_normalVector_zero, ← h0, hpx]
      have hle : inner ℝ (f t) (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) ≤
        inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) := hpmax hmem
      rw [inner_normalVector_pi_div_two, inner_normalVector_pi_div_two] at hle
      linarith
    obtain ⟨hroofD, hroofx, hroofB⟩ := gerver_niche_roof_membership
    refine ⟨p, ⟨hpF.1, ?_⟩, hpx, hpy⟩
    rw [gerver_niche_vertical_fills]
    rintro ((h | h) | h)
    · exact hnofill _ _ hroofD h
    · exact hnofill _ _ hroofx h
    · exact hnofill _ _ hroofB h
  -- ### The support values of the cap
  have hcapy1 : ∀ q ∈ gerverOuterCap, q 1 ≤ 1 := by
    rintro q ⟨-, hc⟩
    have h := (hc 0 h0mem).2
    rw [hpath0, inner_zero_left, inner_tangentVector_zero] at h
    linarith
  have hcapx1 : ∀ q ∈ gerverOuterCap, q 0 ≤ 1 := by
    rintro q ⟨-, hc⟩
    have h := (hc 0 h0mem).1
    rw [hpath0, inner_zero_left, inner_normalVector_zero] at h
    linarith
  have hsupK : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      supportValue gerverOuterCap (t : Real.Angle) =
        inner ℝ (paperGerverPath t) (normalVector (t : Real.Angle)) + 1 ∧
      supportValue gerverOuterCap ((Real.pi / 2 + t : ℝ) : Real.Angle) =
        inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) + 1 := by
    intro t ht
    have hAmem := gerver_outer_contact_A t ht
    have hCmem := gerver_outer_contact_C t ht
    have hang : ((Real.pi / 2 + t : ℝ) : Real.Angle) =
        ((t + Real.pi / 2 : ℝ) : Real.Angle) := by rw [add_comm]
    refine ⟨?_, ?_⟩
    · simp only [supportValue]
      refine IsGreatest.csSup_eq ⟨⟨paperGerverContacts t 0, hAmem, hAn t⟩, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      exact (hz.2 t ht).1
    · rw [supportValue, hang, normalVector_add_pi_div_two_real]
      refine IsGreatest.csSup_eq ⟨⟨paperGerverContacts t 2, hCmem, hCt t⟩, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      exact (hz.2 t ht).2
  -- ### Conjunct 4: the sofa and the cap have the same upper support
  have hGne : gerverLiteralSofa.Nonempty := gerver_literal_connected.1
  have hsupeq : ∀ s ∈ Set.Icc (0 : ℝ) Real.pi,
      supportValue gerverLiteralSofa (s : Real.Angle) =
        supportValue gerverOuterCap (s : Real.Angle) := by
    intro s hs
    have hsin : 0 ≤ Real.sin s := Real.sin_nonneg_of_nonneg_of_le_pi hs.1 hs.2
    refine (supportValue_eq_of_subset_of_inner_le hGne (fun z hz => hz.1)
      (s : Real.Angle) ?_).symm
    intro z hz
    obtain ⟨w, hw, hwx, hwy⟩ := hfiber z hz
    have h1 : inner ℝ z (normalVector (s : Real.Angle)) ≤
        inner ℝ w (normalVector (s : Real.Angle)) := by
      rw [inner_normalVector_real, inner_normalVector_real, hwx]
      have := mul_le_mul_of_nonneg_right hwy hsin
      linarith
    exact h1.trans (inner_le_supportValue_of_isCompact hGcomp hw _)
  have hsupG : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      supportValue gerverLiteralSofa (t : Real.Angle) =
        inner ℝ (paperGerverPath t) (normalVector (t : Real.Angle)) + 1 ∧
      supportValue gerverLiteralSofa ((Real.pi / 2 + t : ℝ) : Real.Angle) =
        inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) + 1 := by
    intro t ht
    refine ⟨?_, ?_⟩
    · rw [hsupeq t ⟨ht.1, by linarith [ht.2, Real.pi_pos]⟩]
      exact (hsupK t ht).1
    · rw [hsupeq (Real.pi / 2 + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩]
      exact (hsupK t ht).2
  -- ### Frame readers for the clockwise motion
  have hinnertan : ∀ (w : Point) (t : ℝ), inner ℝ w (tangentVector (t : Real.Angle)) =
      -(w 0 * Real.sin t) + w 1 * Real.cos t := by
    intro w t
    simp [tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
    ring
  have hmapply : ∀ (t : ℝ) (v p : Point),
      rotateTranslate ((-t : ℝ) : Real.Angle) (-v) p =
        rotationMap ((-t : ℝ) : Real.Angle) (p - v) := by
    intro t v p
    show (EuclideanGeometry.o.rotation ((-t : ℝ) : Real.Angle)) (p + -v) =
      (EuclideanGeometry.o.rotation ((-t : ℝ) : Real.Angle)) (p - v)
    rw [← sub_eq_add_neg]
  have hrotinv : ∀ (t : ℝ) (w : Point),
      rotationMap ((-t : ℝ) : Real.Angle) (rotationMap ((t : ℝ) : Real.Angle) w) = w := by
    intro t w
    show (EuclideanGeometry.o.rotation ((-t : ℝ) : Real.Angle))
      ((EuclideanGeometry.o.rotation ((t : ℝ) : Real.Angle)) w) = w
    rw [Real.Angle.coe_neg, ← Orientation.rotation_symm]
    exact (EuclideanGeometry.o.rotation ((t : ℝ) : Real.Angle)).symm_apply_apply w
  have hcoord0 : ∀ (t : ℝ) (w : Point), rotationMap ((-t : ℝ) : Real.Angle) w 0 =
      inner ℝ w (normalVector (t : Real.Angle)) := by
    intro t w
    rw [rotationMap_apply_zero, inner_normalVector_real, Real.Angle.cos_coe, Real.Angle.sin_coe,
      Real.cos_neg, Real.sin_neg]
    ring
  have hcoord1 : ∀ (t : ℝ) (w : Point), rotationMap ((-t : ℝ) : Real.Angle) w 1 =
      inner ℝ w (tangentVector (t : Real.Angle)) := by
    intro t w
    rw [rotationMap_apply_one, hinnertan, Real.Angle.cos_coe, Real.Angle.sin_coe,
      Real.cos_neg, Real.sin_neg]
    ring
  -- ### Conjunct 3: standard position
  have hsv1 : supportValue gerverLiteralSofa ((Real.pi / 2 : ℝ) : Real.Angle) = 1 := by
    have h := (hsupG 0 h0mem).2
    rw [add_zero, hpath0, inner_zero_left] at h
    linarith
  have hstd : IsStandardPosition gerverLiteralSofa (Real.pi / 2) := by
    refine ⟨hGcomp, ⟨fun r => rotateTranslate ((-(r.val * (Real.pi / 2)) : ℝ) : Real.Angle)
        (-paperGerverPath (r.val * (Real.pi / 2))),
      ⟨gerver_literal_connected, hGcomp.isClosed, ?_, ⟨0, ?_⟩, ?_, ?_, ?_, ?_⟩,
      fun r => -(r.val * (Real.pi / 2)),
      (continuous_subtype_val.mul continuous_const).neg,
      by simp, by simp, ?_⟩,
      hTpos, le_rfl, hsv1, hsv1⟩
    · exact hmotioncont
    · -- the motion starts at the identity
      intro p
      rw [hmapply]
      simp only [Set.Icc.coe_zero, zero_mul, neg_zero, Real.Angle.coe_zero, hpath0,
        sub_zero, add_zero]
      show (EuclideanGeometry.o.rotation 0) p = p
      simp
    · -- each placement is a rotation followed by a translation
      intro r
      refine ⟨(((-(r.val * (Real.pi / 2))) : ℝ) : Real.Angle), fun p => ?_⟩
      rw [hmapply, hmapply]
      simp only [rotationMap, zero_sub, map_sub, map_neg]
      abel
    · -- the initial placement lands in the horizontal arm
      rintro _ ⟨z, hz, rfl⟩
      have heq : rotateTranslate
          ((-((0 : unitInterval).val * (Real.pi / 2)) : ℝ) : Real.Angle)
          (-paperGerverPath ((0 : unitInterval).val * (Real.pi / 2))) z = z := by
        rw [hmapply]
        simp only [Set.Icc.coe_zero, zero_mul, neg_zero, Real.Angle.coe_zero, hpath0,
          sub_zero]
        show (EuclideanGeometry.o.rotation 0) z = z
        simp
      rw [heq]
      exact mem_horizontalHallway_of_coordinates z (hcapx1 z hz.1)
        ⟨hz.1.1, hcapy1 z hz.1⟩
    · -- every intermediate placement lands in the hallway
      intro r
      rintro _ ⟨z, hz, rfl⟩
      have ht : r.val * (Real.pi / 2) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
        ⟨mul_nonneg r.2.1 hTpos.le, by
          nlinarith [r.2.2, hTpos]⟩
      have hzP : z ∈ paperGerverSofa := by rw [paperGerverSofa_eq_literal]; exact hz
      obtain ⟨w, hw, hwz⟩ :=
        Set.mem_iInter₂.1 hzP.2 (r.val * (Real.pi / 2)) ht
      rw [hmapply]
      have hzw : z - paperGerverPath (r.val * (Real.pi / 2)) =
          rotationMap ((r.val * (Real.pi / 2) : ℝ) : Real.Angle) w := by
        rw [← hwz]
        show rotationMap ((r.val * (Real.pi / 2) : ℝ) : Real.Angle) w +
            paperGerverPath (r.val * (Real.pi / 2)) -
            paperGerverPath (r.val * (Real.pi / 2)) =
          rotationMap ((r.val * (Real.pi / 2) : ℝ) : Real.Angle) w
        abel
      rw [hzw, hrotinv]
      exact hw
    · -- the final placement lands in the vertical arm
      rintro _ ⟨z, hz, rfl⟩
      have hTm' : (1 : unitInterval).val * (Real.pi / 2) = Real.pi / 2 := by
        rw [Set.Icc.coe_one, one_mul]
      rw [hmapply]
      refine mem_verticalHallway_of_coordinates _ ⟨?_, ?_⟩ ?_
      · rw [hcoord0, hTm', inner_sub_left, inner_normalVector_pi_div_two,
          inner_normalVector_pi_div_two, hpathTy, sub_zero]
        exact hz.1.1
      · rw [hcoord0, hTm', inner_sub_left, inner_normalVector_pi_div_two,
          inner_normalVector_pi_div_two, hpathTy, sub_zero]
        exact hcapy1 z hz.1
      · rw [hcoord1, hTm', inner_sub_left]
        have h := (hz.1.2 (Real.pi / 2) hTmem).2
        linarith
    · -- the motion realizes the lifted clockwise angle
      intro r p
      rw [hmapply, hmapply]
      simp only [rotationMap, zero_sub, map_sub, map_neg]
      abel
  -- ### Conjunct 5: the paper cap of the sofa is the certified cap
  have hangsum : ∀ t : ℝ, (t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle) =
      ((Real.pi / 2 + t : ℝ) : Real.Angle) := fun t => by
    rw [← Real.Angle.coe_add, add_comm]
  have houter : ∀ t : ℝ,
      (rotatingHallwayParts gerverLiteralSofa (t : Real.Angle)).outerQuadrant =
        normalHalfPlane (t : Real.Angle)
            (supportValue gerverLiteralSofa (t : Real.Angle)) false false ∩
          normalHalfPlane ((t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle))
            (supportValue gerverLiteralSofa
              ((t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle))) false false :=
    fun t => (rotatingHallwayParts_formulas gerverLiteralSofa
      (t : Real.Angle)).2.2.2.2.2.2.2.1
  have hcapOf : capOfSofa gerverLiteralSofa (Real.pi / 2) = gerverOuterCap := by
    ext z
    constructor
    · rintro ⟨hstrip, hint⟩
      rw [mem_stripParallelogram_iff] at hstrip
      refine ⟨hstrip.1.1, fun t ht => ?_⟩
      have hq : z ∈ (rotatingHallwayParts gerverLiteralSofa (t : Real.Angle)).outerQuadrant :=
        Set.mem_iInter₂.1 hint t ht
      rw [houter t] at hq
      have h1 : inner ℝ z (normalVector (t : Real.Angle)) ≤
        supportValue gerverLiteralSofa (t : Real.Angle) := hq.1
      have h2 : inner ℝ z
          (normalVector ((t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle))) ≤
        supportValue gerverLiteralSofa
          ((t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle)) := hq.2
      rw [normalVector_add_pi_div_two, hangsum t, (hsupG t ht).2] at h2
      rw [(hsupG t ht).1] at h1
      exact ⟨h1, h2⟩
    · intro hz
      refine ⟨?_, Set.mem_iInter₂.2 fun t ht => ?_⟩
      · rw [mem_stripParallelogram_iff, inner_normalVector_pi_div_two]
        exact ⟨⟨hz.1, hcapy1 z hz⟩, hz.1, hcapy1 z hz⟩
      · rw [houter t]
        refine ⟨?_, ?_⟩
        · show inner ℝ z (normalVector (t : Real.Angle)) ≤
            supportValue gerverLiteralSofa (t : Real.Angle)
          rw [(hsupG t ht).1]
          exact (hz.2 t ht).1
        · show inner ℝ z
              (normalVector ((t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle))) ≤
            supportValue gerverLiteralSofa
              ((t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle))
          rw [normalVector_add_pi_div_two, hangsum t, (hsupG t ht).2]
          exact (hz.2 t ht).2
  -- ### Conjunct 6: the cap representative and its contact faces
  have hfaces : ∃ K : CapSpace (Real.pi / 2), (K.val : Set Point) = gerverOuterCap ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        exposedEdge K.val (t : Real.Angle) = {paperGerverContacts t 0} ∧
        exposedEdge K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) = {paperGerverContacts t 2}) ∧
      paperGerverContacts 0 0 = (edgeVertices K.val (0 : Real.Angle)).1 ∧
      paperGerverContacts (Real.pi / 2) 0 =
        (edgeVertices K.val ((Real.pi / 2 : ℝ) : Real.Angle)).2 ∧
      paperGerverContacts 0 2 = (edgeVertices K.val ((Real.pi / 2 : ℝ) : Real.Angle)).1 ∧
      paperGerverContacts (Real.pi / 2) 2 = (edgeVertices K.val (Real.pi : Real.Angle)).2 := by
    -- a plane point is determined by its two frame coordinates
    have hpteq : ∀ (a : Real.Angle) (p q : Point),
        inner ℝ p (normalVector a) = inner ℝ q (normalVector a) →
        inner ℝ p (tangentVector a) = inner ℝ q (tangentVector a) → p = q := by
      intro a p q h1 h2
      rw [← inner_normalVector_smul_add_inner_tangentVector_smul p a,
        ← inner_normalVector_smul_add_inner_tangentVector_smul q a, h1, h2]
    have hdx : ∀ t : ℝ, HasDerivAt paperGerverPath (deriv paperGerverPath t) t := fun t => by
      rw [deriv_paperGerverPath hC1 t]
      exact hasDerivAt_paperGerverPath hC1 t
    -- exposed faces of the certified body, read in the cap's own description
    have hexp : ∀ (a : Real.Angle) (z : Point), z ∈ exposedEdge Kb a ↔
        (z ∈ gerverOuterCap ∧
          inner ℝ z (normalVector a) = supportValue gerverOuterCap a) := by
      intro a z
      constructor
      · intro h
        refine ⟨hKset ▸ h.1, ?_⟩
        have h2 : inner ℝ z (normalVector a) = supportValue (Kb : Set Point) a := h.2
        rwa [hKset] at h2
      · intro h
        refine ⟨hKset ▸ h.1, ?_⟩
        show inner ℝ z (normalVector a) = supportValue (Kb : Set Point) a
        rw [hKset]
        exact h.2
    have hsingleV : ∀ (a : Real.Angle) (p : Point), exposedEdge Kb a = {p} →
        (edgeVertices Kb a).1 = p ∧ (edgeVertices Kb a).2 = p := fun a p h =>
      ⟨Set.mem_singleton_iff.1 (h ▸ edgeVertices_fst_mem Kb a),
        Set.mem_singleton_iff.1 (h ▸ edgeVertices_snd_mem Kb a)⟩
    -- interior uniqueness in the normal family
    have hnormaledge : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ∀ z ∈ gerverOuterCap,
        inner ℝ z (normalVector (t : Real.Angle)) =
          inner ℝ (paperGerverPath t) (normalVector (t : Real.Angle)) + 1 →
        z = paperGerverContacts t 0 := by
      intro t ht z hz heq
      have hgd : HasDerivAt (fun s : ℝ =>
          (inner ℝ (paperGerverPath s) (normalVector (s : Real.Angle)) + 1) -
            inner ℝ z (normalVector (s : Real.Angle)))
          ((inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) +
            (paperGerverVelocityComponents t).1) -
            inner ℝ z (tangentVector (t : Real.Angle))) t :=
        (((hdx t).inner ℝ (hasDerivAt_normalVector t)).add_const 1).sub
          (hasDerivAt_inner_normalVector z t)
      have hgmin : IsLocalMin (fun s : ℝ =>
          (inner ℝ (paperGerverPath s) (normalVector (s : Real.Angle)) + 1) -
            inner ℝ z (normalVector (s : Real.Angle))) t := by
        refine IsMinOn.isLocalMin ?_ (Icc_mem_nhds ht.1 ht.2)
        intro s hs
        have h := (hz.2 s hs).1
        show (inner ℝ (paperGerverPath t) (normalVector (t : Real.Angle)) + 1) -
            inner ℝ z (normalVector (t : Real.Angle)) ≤
          (inner ℝ (paperGerverPath s) (normalVector (s : Real.Angle)) + 1) -
            inner ℝ z (normalVector (s : Real.Angle))
        linarith
      have hzero := hgmin.hasDerivAt_eq_zero hgd
      refine hpteq (t : Real.Angle) z (paperGerverContacts t 0) ?_ ?_
      · rw [hAn t]; exact heq
      · rw [hAt t]; linarith
    -- interior uniqueness in the tangent family
    have htangentedge : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ∀ z ∈ gerverOuterCap,
        inner ℝ z (tangentVector (t : Real.Angle)) =
          inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) + 1 →
        z = paperGerverContacts t 2 := by
      intro t ht z hz heq
      have hzt : HasDerivAt (fun s : ℝ => inner ℝ z (tangentVector (s : Real.Angle)))
          (-inner ℝ z (normalVector (t : Real.Angle))) t := by
        simpa using (hasDerivAt_const t z).inner ℝ (hasDerivAt_tangentVector t)
      have hgd : HasDerivAt (fun s : ℝ =>
          (inner ℝ (paperGerverPath s) (tangentVector (s : Real.Angle)) + 1) -
            inner ℝ z (tangentVector (s : Real.Angle)))
          ((inner ℝ (paperGerverPath t) (-normalVector (t : Real.Angle)) +
            (paperGerverVelocityComponents t).2) -
            -inner ℝ z (normalVector (t : Real.Angle))) t :=
        (((hdx t).inner ℝ (hasDerivAt_tangentVector t)).add_const 1).sub hzt
      have hgmin : IsLocalMin (fun s : ℝ =>
          (inner ℝ (paperGerverPath s) (tangentVector (s : Real.Angle)) + 1) -
            inner ℝ z (tangentVector (s : Real.Angle))) t := by
        refine IsMinOn.isLocalMin ?_ (Icc_mem_nhds ht.1 ht.2)
        intro s hs
        have h := (hz.2 s hs).2
        show (inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) + 1) -
            inner ℝ z (tangentVector (t : Real.Angle)) ≤
          (inner ℝ (paperGerverPath s) (tangentVector (s : Real.Angle)) + 1) -
            inner ℝ z (tangentVector (s : Real.Angle))
        linarith
      have hzero := hgmin.hasDerivAt_eq_zero hgd
      rw [inner_neg_right] at hzero
      refine hpteq (t : Real.Angle) z (paperGerverContacts t 2) ?_ ?_
      · rw [hCn t]; linarith
      · rw [hCt t]; exact heq
    -- the interior exposed faces are the two contact singletons
    have hedgeA : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        exposedEdge Kb (t : Real.Angle) = {paperGerverContacts t 0} := by
      intro t ht
      have htI : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := Set.Ioo_subset_Icc_self ht
      refine Set.eq_singleton_iff_unique_mem.2
        ⟨(hexp _ _).2 ⟨gerver_outer_contact_A t htI, ?_⟩, fun z hz => ?_⟩
      · rw [hAn t, (hsupK t htI).1]
      · rw [hexp] at hz
        exact hnormaledge t ht z hz.1 (by rw [hz.2, (hsupK t htI).1])
    have hedgeC : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        exposedEdge Kb ((t + Real.pi / 2 : ℝ) : Real.Angle) = {paperGerverContacts t 2} := by
      intro t ht
      have htI : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := Set.Ioo_subset_Icc_self ht
      have hang : ((t + Real.pi / 2 : ℝ) : Real.Angle) =
          ((Real.pi / 2 + t : ℝ) : Real.Angle) := by rw [add_comm]
      have hsv : supportValue gerverOuterCap ((t + Real.pi / 2 : ℝ) : Real.Angle) =
          inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) + 1 := by
        rw [hang]; exact (hsupK t htI).2
      refine Set.eq_singleton_iff_unique_mem.2
        ⟨(hexp _ _).2 ⟨gerver_outer_contact_C t htI, ?_⟩, fun z hz => ?_⟩
      · rw [normalVector_add_pi_div_two_real, hCt t, hsv]
      · rw [hexp] at hz
        refine htangentedge t ht z hz.1 ?_
        have h := hz.2
        rwa [normalVector_add_pi_div_two_real, hsv] at h
    -- the four contact curves are continuous
    have hcontacts : Continuous paperGerverContacts := paperGerverContactData_properties.2.1
    have hcontA : Continuous fun s : ℝ => paperGerverContacts s 0 :=
      (continuous_apply 0).comp hcontacts
    have hcontC : Continuous fun s : ℝ => paperGerverContacts s 2 :=
      (continuous_apply 2).comp hcontacts
    -- vertex limits at the four endpoints
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    have heventA : ∀ᶠ s : ℝ in nhdsWithin 0 (Set.Ioi 0),
        paperGerverContacts s 0 = (edgeVertices Kb (s : Real.Angle)).1 := by
      filter_upwards [Ioo_mem_nhdsGT hTpos] with s hs
      exact ((hsingleV _ _ (hedgeA s hs)).1).symm
    have heventA' : ∀ᶠ s : ℝ in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
        paperGerverContacts s 0 = (edgeVertices Kb (s : Real.Angle)).1 := by
      filter_upwards [Ioo_mem_nhdsLT hTpos] with s hs
      exact ((hsingleV _ _ (hedgeA s hs)).1).symm
    have hCshift : ∀ s : ℝ, s ∈ Set.Ioo (Real.pi / 2) Real.pi →
        paperGerverContacts (s - Real.pi / 2) 2 = (edgeVertices Kb (s : Real.Angle)).1 := by
      intro s hs
      have hs' : s - Real.pi / 2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
        ⟨by linarith [hs.1], by linarith [hs.2]⟩
      have hang : ((s : ℝ) : Real.Angle) =
          ((s - Real.pi / 2 + Real.pi / 2 : ℝ) : Real.Angle) := by rw [sub_add_cancel]
      rw [hang]
      exact ((hsingleV _ _ (hedgeC (s - Real.pi / 2) hs')).1).symm
    have heventC : ∀ᶠ s : ℝ in nhdsWithin (Real.pi / 2) (Set.Ioi (Real.pi / 2)),
        paperGerverContacts (s - Real.pi / 2) 2 = (edgeVertices Kb (s : Real.Angle)).1 := by
      filter_upwards [Ioo_mem_nhdsGT (show Real.pi / 2 < Real.pi by linarith)] with s hs
      exact hCshift s hs
    have heventC' : ∀ᶠ s : ℝ in nhdsWithin Real.pi (Set.Iio Real.pi),
        paperGerverContacts (s - Real.pi / 2) 2 = (edgeVertices Kb (s : Real.Angle)).1 := by
      filter_upwards [Ioo_mem_nhdsLT (show Real.pi / 2 < Real.pi by linarith)] with s hs
      exact hCshift s hs
    have hcontCshift : Continuous fun s : ℝ => paperGerverContacts (s - Real.pi / 2) 2 :=
      hcontC.comp (continuous_id.sub continuous_const)
    refine ⟨⟨Kb, hKcap⟩, hKset, fun t ht => ⟨hedgeA t ht, hedgeC t ht⟩, ?_, ?_, ?_, ?_⟩
    · rw [← Real.Angle.coe_zero]
      refine tendsto_nhds_unique ?_ (contact_oneSided_limits Kb 0).1
      exact Filter.Tendsto.congr' heventA ((hcontA.tendsto 0).mono_left nhdsWithin_le_nhds)
    · refine tendsto_nhds_unique ?_ (contact_oneSided_limits Kb (Real.pi / 2)).2.2.2.1
      exact Filter.Tendsto.congr' heventA'
        ((hcontA.tendsto (Real.pi / 2)).mono_left nhdsWithin_le_nhds)
    · refine tendsto_nhds_unique ?_ (contact_oneSided_limits Kb (Real.pi / 2)).1
      have h : Filter.Tendsto (fun s : ℝ => paperGerverContacts (s - Real.pi / 2) 2)
          (nhdsWithin (Real.pi / 2) (Set.Ioi (Real.pi / 2)))
          (nhds (paperGerverContacts 0 2)) := by
        have := (hcontCshift.tendsto (Real.pi / 2)).mono_left
          (nhdsWithin_le_nhds (s := Set.Ioi (Real.pi / 2)))
        rwa [sub_self] at this
      exact Filter.Tendsto.congr' heventC h
    · refine tendsto_nhds_unique ?_ (contact_oneSided_limits Kb Real.pi).2.2.2.1
      have h : Filter.Tendsto (fun s : ℝ => paperGerverContacts (s - Real.pi / 2) 2)
          (nhdsWithin Real.pi (Set.Iio Real.pi))
          (nhds (paperGerverContacts (Real.pi / 2) 2)) := by
        have := (hcontCshift.tendsto Real.pi).mono_left
          (nhdsWithin_le_nhds (s := Set.Iio Real.pi))
        rwa [show Real.pi - Real.pi / 2 = Real.pi / 2 by ring] at this
      exact Filter.Tendsto.congr' heventC' h
  refine ⟨hfiber, paperGerverSofa_eq_literal, hstd, hsupeq, hcapOf, hfaces, ?_⟩
  rintro S (rfl | rfl)
  · exact hsupK
  · exact hsupG

end MovingSofa
