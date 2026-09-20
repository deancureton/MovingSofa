import MovingSofa.Analysis.SurfaceMeasure.Properties
import MovingSofa.Cap.HalfPlanes

/-!
# The surface area measure of a right-angle cap at its lower normals

A right-angle cap lies above its base line and is stable under vertical projection onto it, so
at a strictly downward normal direction the support value is attained only on the base line, at
whichever horizontal extremum the sign of the horizontal normal component selects.  Both open
quarter arcs of lower normals therefore carry faces that degenerate to a single base corner,
and the surface area measure vanishes on them
(`MovingSofa.CapSpace.surfaceAreaMeasure_image_Ioo_lower_eq_zero`).  Outside the closed upper
semicircle only the bottom normal `3π / 2` is left, so an integrand vanishing there integrates
to zero (`MovingSofa.CapSpace.setIntegral_compl_image_Icc_zero_pi_eq_zero`).
-/

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- At a strictly downward normal direction the face of a right-angle cap degenerates to the
base point below a horizontal extremum: positive height strictly lowers the normal coordinate,
and on the base line the sign of `Real.cos t` selects a horizontal extremum. -/
theorem CapSpace.exposedEdge_subset_singleton_of_isMaxOn (K : CapSpace (Real.pi / 2))
    {q : Point} (hq : q ∈ (K.val : Set Point)) {t : ℝ} (hcos : Real.cos t ≠ 0)
    (hsin : Real.sin t < 0)
    (hmax : IsMaxOn (fun p : Point ↦ p 0 * Real.cos t) (K.val : Set Point) q) :
    exposedEdge K.val (t : Real.Angle) ⊆
      {q - q 1 • normalVector ((Real.pi / 2 : ℝ) : Real.Angle)} := by
  have hflat0 : (q - q 1 • normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) 0 = q 0 := by
    simp [normalVector, frame]
  have hflat1 : (q - q 1 • normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) 1 = 0 := by
    simp [normalVector, frame]
  intro p hp
  have hpK : p ∈ (K.val : Set Point) := hp.1
  have hp1 : 0 ≤ p 1 := by
    simpa only [inner_normalVector_pi_div_two] using K.inner_normalVector_pi_div_two_nonneg hpK
  have hpsup : inner ℝ p (normalVector (t : Real.Angle)) =
    supportValue K.val (t : Real.Angle) := hp.2
  have hple : inner ℝ (q - q 1 • normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
      (normalVector (t : Real.Angle)) ≤ inner ℝ p (normalVector (t : Real.Angle)) := by
    rw [hpsup]
    exact inner_le_supportValue K.val (K.base_projection_mem hq) _
  rw [inner_normalVector_real, inner_normalVector_real, hflat0, hflat1] at hple
  have h1 : p 0 * Real.cos t ≤ q 0 * Real.cos t := isMaxOn_iff.mp hmax p hpK
  have h2 : p 1 * Real.sin t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hp1 hsin.le
  have he1 : p 0 * Real.cos t = q 0 * Real.cos t := by linarith
  have he2 : p 1 = 0 := by
    have h3 : p 1 * Real.sin t = 0 := by linarith
    exact (mul_eq_zero.mp h3).resolve_right hsin.ne
  have g0 : p 0 = (q - q 1 • normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) 0 := by
    rw [hflat0]; exact mul_right_cancel₀ hcos he1
  have g1 : p 1 = (q - q 1 • normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) 1 := by
    rw [hflat1]; exact he2
  have hpt : p = q - q 1 • normalVector ((Real.pi / 2 : ℝ) : Real.Angle) := by
    ext i
    fin_cases i
    · exact g0
    · exact g1
  simpa only [Set.mem_singleton_iff] using hpt

/-- The two base corners of a right-angle cap: on the open lower left quarter of normals every
face degenerates to the base point below a leftmost point of the cap, and on the open lower
right quarter to the base point below a rightmost one. -/
theorem CapSpace.exists_exposedEdge_subset_singleton (K : CapSpace (Real.pi / 2)) :
    ∃ pl pr : Point,
      (∀ t : ℝ, Real.cos t < 0 → Real.sin t < 0 →
        exposedEdge K.val (t : Real.Angle) ⊆ {pl}) ∧
      ∀ t : ℝ, 0 < Real.cos t → Real.sin t < 0 →
        exposedEdge K.val (t : Real.Angle) ⊆ {pr} := by
  have hcont : Continuous fun q : Point ↦ q 0 := PiLp.continuous_apply 2 _ 0
  obtain ⟨ql, hql, hqlmin⟩ :=
    K.val.isCompact.exists_isMinOn K.val.nonempty hcont.continuousOn
  obtain ⟨qr, hqr, hqrmax⟩ :=
    K.val.isCompact.exists_isMaxOn K.val.nonempty hcont.continuousOn
  refine ⟨ql - ql 1 • normalVector ((Real.pi / 2 : ℝ) : Real.Angle),
    qr - qr 1 • normalVector ((Real.pi / 2 : ℝ) : Real.Angle), ?_, ?_⟩
  · exact fun t hcos hsin ↦ K.exposedEdge_subset_singleton_of_isMaxOn hql hcos.ne hsin
      (isMaxOn_iff.mpr fun p hp ↦
        mul_le_mul_of_nonpos_right (isMinOn_iff.mp hqlmin p hp) hcos.le)
  · exact fun t hcos hsin ↦ K.exposedEdge_subset_singleton_of_isMaxOn hqr hcos.ne' hsin
      (isMaxOn_iff.mpr fun p hp ↦
        mul_le_mul_of_nonneg_right (isMaxOn_iff.mp hqrmax p hp) hcos.le)

/-- The surface area measure of a right-angle cap vanishes on both open quarter arcs of lower
normals, because there every face degenerates to a single base corner. -/
theorem CapSpace.surfaceAreaMeasure_image_Ioo_lower_eq_zero (K : CapSpace (Real.pi / 2)) :
    surfaceAreaMeasure K.val
        ((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo Real.pi (3 * Real.pi / 2)) = 0 ∧
      surfaceAreaMeasure K.val
        ((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo (3 * Real.pi / 2) (2 * Real.pi)) = 0 := by
  have hpi := Real.pi_pos
  obtain ⟨pl, pr, hl, hr⟩ := K.exists_exposedEdge_subset_singleton
  have hsin : ∀ s : ℝ, Real.pi < s → s < 2 * Real.pi → Real.sin s < 0 := by
    intro s h1 h2
    have h := Real.sin_pos_of_pos_of_lt_pi (x := s - Real.pi) (by linarith) (by linarith)
    rw [Real.sin_sub_pi] at h
    linarith
  have main : ∀ (a b : ℝ) (p : Point), a ≤ b → b < a + Real.pi →
      (∀ s ∈ Set.Ioo a b, exposedEdge K.val (s : Real.Angle) ⊆ {p}) →
      surfaceAreaMeasure K.val ((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b) = 0 := by
    intro a b p hab hba hsub
    refine surfaceAreaMeasure_null_of_exposedEdge_subset_singleton K.val
      (Real.Angle.isOpen_image_Ioo a b).measurableSet hab hba
      (Set.image_mono Set.Ioo_subset_Icc_self) p ?_
    intro u hu
    obtain ⟨s, hs, rfl⟩ := hu
    exact hsub s hs
  refine ⟨main Real.pi (3 * Real.pi / 2) pl (by linarith) (by linarith) fun s hs ↦ ?_,
    main (3 * Real.pi / 2) (2 * Real.pi) pr (by linarith) (by linarith) fun s hs ↦ ?_⟩
  · exact hl s (Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith [hs.1]) (by linarith [hs.2]))
      (hsin s hs.1 (by linarith [hs.2]))
  · refine hr s ?_ (hsin s (by linarith [hs.1]) hs.2)
    have h := Real.cos_pos_of_mem_Ioo
      (x := s - 2 * Real.pi) ⟨by linarith [hs.1], by linarith [hs.2]⟩
    rwa [Real.cos_sub_two_pi] at h

/-- Outside the closed upper semicircle the surface area measure of a right-angle cap is carried
by the single downward normal `3π / 2`, so any integrand vanishing there integrates to zero. -/
theorem CapSpace.setIntegral_compl_image_Icc_zero_pi_eq_zero (K : CapSpace (Real.pi / 2))
    (f : Real.Angle → ℝ) (hf : f ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0) :
    ∫ t in ((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Icc 0 Real.pi)ᶜ,
      f t ∂surfaceAreaMeasure K.val = 0 := by
  obtain ⟨hA, hB⟩ := K.surfaceAreaMeasure_image_Ioo_lower_eq_zero
  have hS : MeasurableSet ((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Icc 0 Real.pi) :=
    (isCompact_Icc.image Real.Angle.continuous_coe).isClosed.measurableSet
  have haenot : ∀ᵐ t ∂surfaceAreaMeasure K.val,
      t ∉ ((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo Real.pi (3 * Real.pi / 2)) ∪
        ((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo (3 * Real.pi / 2) (2 * Real.pi)) := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using measure_union_null hA hB
  have hcongr : ∫ t in ((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Icc 0 Real.pi)ᶜ,
      f t ∂surfaceAreaMeasure K.val =
      ∫ _t in ((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Icc 0 Real.pi)ᶜ,
        (0 : ℝ) ∂surfaceAreaMeasure K.val := by
    refine setIntegral_congr_ae hS.compl ?_
    filter_upwards [haenot] with t ht hts
    have hcoe : ((t.toReal + 2 * Real.pi : ℝ) : Real.Angle) = t := by
      rw [Real.Angle.coe_add, Real.Angle.coe_two_pi, add_zero, Real.Angle.coe_toReal]
    have hneg : t.toReal < 0 := by
      by_contra hge
      exact hts ⟨t.toReal, ⟨not_lt.mp hge, Real.Angle.toReal_le_pi t⟩, t.coe_toReal⟩
    have hlow : Real.pi < t.toReal + 2 * Real.pi :=
      by linarith [Real.Angle.neg_pi_lt_toReal t]
    have hmid : t = ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
      rcases lt_trichotomy (t.toReal + 2 * Real.pi) (3 * Real.pi / 2) with h | h | h
      · exact absurd (Or.inl ⟨t.toReal + 2 * Real.pi, ⟨hlow, h⟩, hcoe⟩) ht
      · rw [← hcoe, h]
      · exact absurd (Or.inr ⟨t.toReal + 2 * Real.pi, ⟨h, by linarith⟩, hcoe⟩) ht
    rw [hmid, hf]
  rw [hcongr, integral_zero]

end MovingSofa
