import MovingSofa.Analysis.SurfaceMeasure.OppositeDensity
import MovingSofa.Gerver.TailGeometry

/-!
# The four contact densities of Gerver's cap

The rotating frame reads the four contact curves of Gerver's sofa as angular densities of two
surface measures: the two outer contacts `A`, `C` against the cap `K = C(G)` itself, and the two
inner contacts `B`, `D` against the two tail bodies through the opposite surface measure.

The two outer clauses are exactly the certified cap densities `gerver_surface_densities`,
rewritten with the tautological identity `⟨r • v_t, v_t⟩ = r` and translated by the quarter
turn that separates the `A` arc from the `C` arc.  The two inner clauses use that `B = A - u` and
`D = C - v` are the outer contacts translated by a frame vector, so each closed stage carries a
globally differentiable branch curve for them (`exists_branch_paperGerverContacts_one`,
`exists_branch_paperGerverContacts_three`); the tail geometry identifies those curves with the
positive vertices of the two tail bodies at the opposite normal, and
`oppositeSurfaceData_angleImage_eq_withDensity` turns each stage into a Lebesgue density.  The
stages are glued with `measure_angleImage_eq_of_union`, which puts every interior switch inside a
window that is closed on the right, so the only atom to compute is the one at the included left
endpoint `t₃` of the `B` arc.
-/

noncomputable section

open MeasureTheory

namespace MovingSofa

def angularDensityMeasure (f : ℝ → ℝ) (S : Set ℝ) : Measure Real.Angle :=
  Measure.map (fun t : ℝ ↦ (t : Real.Angle))
    ((volume.restrict S).withDensity (fun t ↦ ENNReal.ofReal (f t)))

def HasAngularDensity (μ : Measure Real.Angle) (f : ℝ → ℝ) (S : Set ℝ) : Prop :=
  Integrable f (volume.restrict S) ∧ (∀ᵐ t ∂volume.restrict S, 0 ≤ f t) ∧
    μ.restrict ((fun t : ℝ ↦ (t : Real.Angle)) '' S) = angularDensityMeasure f S

/-- An angular density identity on a window of at most one turn computes the measure of the
angular image of every measurable subset of the window. -/
theorem HasAngularDensity.angleImage_eq_setLIntegral {μ : Measure Real.Angle} {f : ℝ → ℝ}
    {S : Set ℝ} (h : HasAngularDensity μ f S) {a b : ℝ} (hturn : b ≤ a + 2 * Real.pi)
    (hS : S ⊆ Set.Ioc a b) {T : Set ℝ} (hT : MeasurableSet T) (hTS : T ⊆ S) :
    μ ((fun t : ℝ ↦ (t : Real.Angle)) '' T) =
      ∫⁻ t in T, ENNReal.ofReal (f t) ∂volume := by
  have himage : MeasurableSet ((fun t : ℝ ↦ (t : Real.Angle)) '' T) :=
    Real.Angle.measurableSet_image_of_subset_Ioc hturn hT (hTS.trans hS)
  have hrestrict : μ ((fun t : ℝ ↦ (t : Real.Angle)) '' T) =
      μ.restrict ((fun t : ℝ ↦ (t : Real.Angle)) '' S)
        ((fun t : ℝ ↦ (t : Real.Angle)) '' T) := by
    rw [Measure.restrict_apply himage, Set.inter_eq_left.2 (Set.image_mono hTS)]
  rw [hrestrict, h.2.2, angularDensityMeasure,
    Real.Angle.map_coe_withDensity_image_eq_setLIntegral hturn hS hT hTS]

theorem gerver_measureTranslation (K : SpecialCapSpace) (B D : ConvexBody Point)
    (hK : (K.val.val : Set Point) = capOfSofa paperGerverSofa (Real.pi / 2))
    (hB : (B : Set Point) = (canonicalTailSets K).1)
    (hD : (D : Set Point) = (canonicalTailSets K).2) :
    HasAngularDensity (surfaceAreaMeasure K.val.val)
      (fun t ↦ inner ℝ (deriv (fun s ↦ paperGerverContacts s 0) t)
        (tangentVector (t : Real.Angle))) (Set.Ico 0 (Real.pi / 2)) ∧
    HasAngularDensity (oppositeSurfaceData B).1
      (fun t ↦ inner ℝ (-(deriv (fun s ↦ paperGerverContacts s 1) t))
        (tangentVector (t : Real.Angle)))
      (Set.Ico (gerverStageTimes 3) (gerverStageTimes 5)) ∧
    HasAngularDensity (surfaceAreaMeasure K.val.val)
      (fun t ↦ inner ℝ (-(deriv (fun s ↦ paperGerverContacts s 2) (t - Real.pi / 2)))
        (normalVector ((t - Real.pi / 2 : ℝ) : Real.Angle)))
      (Set.Ioc (Real.pi / 2) Real.pi) ∧
    HasAngularDensity (oppositeSurfaceData D).1
      (fun t ↦ inner ℝ (deriv (fun s ↦ paperGerverContacts s 3) (t - Real.pi / 2))
        (normalVector ((t - Real.pi / 2 : ℝ) : Real.Angle)))
      (Set.Ioc (Real.pi / 2 + gerverStageTimes 0)
        (Real.pi / 2 + gerverStageTimes 2)) := by
  -- ### The strictly increasing stage times
  have h0 : gerverStageTimes 0 = 0 := gerverStageTimes_zero
  have h5 : gerverStageTimes 5 = Real.pi / 2 := rfl
  have h01 : gerverStageTimes 0 < gerverStageTimes 1 := gerverStageTimes_strictMono (by decide)
  have h12 : gerverStageTimes 1 < gerverStageTimes 2 := gerverStageTimes_strictMono (by decide)
  have h23 : gerverStageTimes 2 < gerverStageTimes 3 := gerverStageTimes_strictMono (by decide)
  have h34 : gerverStageTimes 3 < gerverStageTimes 4 := gerverStageTimes_strictMono (by decide)
  have h45 : gerverStageTimes 4 < gerverStageTimes 5 := gerverStageTimes_strictMono (by decide)
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  -- ### The certified cap carries the two envelope densities
  obtain ⟨K', hK'set, r, sden, hdens, ⟨M, hM⟩, hstage⟩ := gerver_surface_densities
  have hKeq : K' = K.val := Subtype.ext (SetLike.coe_injective (hK'set.trans hK.symm))
  subst hKeq
  -- ### The two tails are traced by the two inner contact curves
  obtain ⟨htailD, htailB, -, -, htailD2, -, -, -, htailB3, -, -, -⟩ :=
    gerver_tailGeometry K B D hK hB hD
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- ### (1) the outer contact `A` against the moving tangent on `[0, π/2)`
    have haeval : ∀ᵐ t ∂volume.restrict (Set.Ico (0 : ℝ) (Real.pi / 2)),
        inner ℝ (deriv (fun s ↦ paperGerverContacts s 0) t) (tangentVector (t : Real.Angle)) =
          (r t : ℝ) := by
      filter_upwards [ae_mem_openStage 0 (S := Set.Ico (0 : ℝ) (Real.pi / 2)) measurableSet_Ico
        (fun t ht ↦ ⟨ht.1, by linarith [ht.2]⟩)] with t ht
      obtain ⟨j, hj⟩ := ht
      rw [sub_zero] at hj
      rw [(hstage j t hj).1.deriv, real_inner_smul_left, inner_tangentVector_self, mul_one]
    have hrint : Integrable (fun t ↦ ((r t : ℝ)))
        (volume.restrict (Set.Ico (0 : ℝ) (Real.pi / 2))) := by
      have hfin : IsFiniteMeasure (volume.restrict (Set.Ico (0 : ℝ) (Real.pi / 2))) := by
        refine ⟨?_⟩
        rw [Measure.restrict_apply_univ, Real.volume_Ico]
        exact ENNReal.ofReal_lt_top
      refine Integrable.mono' (integrable_const M)
        hdens.1.coe_nnreal_real.aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (r t).coe_nonneg]
      exact (hM t ⟨ht.1, ht.2.le⟩).1
    refine ⟨hrint.congr (Filter.EventuallyEq.symm haeval), ?_, ?_⟩
    · filter_upwards [haeval] with t ht
      rw [ht]
      exact (r t).coe_nonneg
    · rw [hdens.2.2.1, angularDensityMeasure]
      congr 1
      refine withDensity_congr_ae ?_
      filter_upwards [haeval] with t ht
      rw [ht, ENNReal.ofReal_coe_nnreal]
  · -- ### (2) the inner contact `B` against the moving tangent on `[t₃, t₅)`
    obtain ⟨fB, hfBdef⟩ : ∃ f : ℝ → ℝ, f = fun t ↦ inner ℝ
        (-(deriv (fun s ↦ paperGerverContacts s 1) t)) (tangentVector (t : Real.Angle)) :=
      ⟨_, rfl⟩
    rw [← hfBdef]
    obtain ⟨F3, g3, hF3, hg3, hg3nn, hFeq3⟩ :=
      exists_branch_paperGerverContacts_one (i := 3) (Or.inl rfl)
    obtain ⟨F4, g4, hF4, hg4, hg4nn, hFeq4⟩ :=
      exists_branch_paperGerverContacts_one (i := 4) (Or.inr rfl)
    -- the positive vertex of `B` at normal `π + s` is the inner contact
    have hvB : ∀ s ∈ Set.Ico (gerverStageTimes 3) (gerverStageTimes 5),
        (edgeVertices B ((Real.pi + s : ℝ) : Real.Angle)).1 = paperGerverContacts s 1 := by
      intro s hs
      rcases eq_or_lt_of_le hs.1 with heq | hlt
      · rw [← heq, htailB3]
      · rw [htailB s ⟨hlt, hs.2⟩]
    -- the target density is the branch speed inside each of the two open stages
    have hfB3 : ∀ t ∈ Set.Ioo (gerverStageTimes 3) (gerverStageTimes 4), fB t = g3 t := by
      intro t ht
      simp only [hfBdef]
      rw [(hasDerivAt_of_eqOn_stage hF3 hFeq3 ht).deriv, neg_smul, neg_neg, real_inner_smul_left,
        inner_tangentVector_self, mul_one]
    have hfB4 : ∀ t ∈ Set.Ioo (gerverStageTimes 4) (gerverStageTimes 5), fB t = g4 t := by
      intro t ht
      simp only [hfBdef]
      rw [(hasDerivAt_of_eqOn_stage hF4 hFeq4 ht).deriv, neg_smul, neg_neg, real_inner_smul_left,
        inner_tangentVector_self, mul_one]
    -- the two stage windows
    have hagree3 : ∀ T, MeasurableSet T →
        T ⊆ Set.Ioc (gerverStageTimes 3) (gerverStageTimes 4) →
        (oppositeSurfaceData B).1 ((fun s : ℝ ↦ (s : Real.Angle)) '' T) =
          volume.withDensity (fun s ↦ ENNReal.ofReal (fB s)) T := by
      intro T hT hTsub
      refine oppositeSurfaceData_angleImage_eq_withDensity B h34 (by linarith) F3 fB g3 hF3 hg3
        hg3nn hfB3 ?_ hT hTsub
      exact fun s hs ↦ (hvB s ⟨hs.1, by linarith [hs.2]⟩).trans (hFeq3 s hs)
    have hagree4 : ∀ T, MeasurableSet T →
        T ⊆ Set.Ioo (gerverStageTimes 4) (gerverStageTimes 5) →
        (oppositeSurfaceData B).1 ((fun s : ℝ ↦ (s : Real.Angle)) '' T) =
          volume.withDensity (fun s ↦ ENNReal.ofReal (fB s)) T := by
      intro T hT hTsub
      refine oppositeSurfaceData_angleImage_eq_withDensity_of_openRight B h45 (by linarith) F4 fB
        g4 hF4 hg4 (fun s hs ↦ hg4nn s ⟨hs.1, hs.2.le⟩) hfB4 ?_ hT hTsub
      exact fun s hs ↦ (hvB s ⟨by linarith [hs.1], hs.2⟩).trans (hFeq4 s ⟨hs.1, hs.2.le⟩)
    -- the included left endpoint carries no surface atom
    have hatom : (oppositeSurfaceData B).1
        ((fun s : ℝ ↦ (s : Real.Angle)) '' {gerverStageTimes 3}) = 0 := by
      rw [oppositeSurfaceData_angleImage B
        (by rw [Set.image_singleton]; exact measurableSet_singleton _),
        Set.image_singleton, Set.image_singleton,
        (surfaceAreaMeasure_atom_length B
          ((gerverStageTimes 3 + Real.pi : ℝ) : Real.Angle)).2.1,
        show ((gerverStageTimes 3 + Real.pi : ℝ) : Real.Angle) =
          ((Real.pi + gerverStageTimes 3 : ℝ) : Real.Angle) from by rw [add_comm], htailB3]
      simp
    have hagreeAtom : ∀ T, MeasurableSet T → T ⊆ {gerverStageTimes 3} →
        (oppositeSurfaceData B).1 ((fun s : ℝ ↦ (s : Real.Angle)) '' T) =
          volume.withDensity (fun s ↦ ENNReal.ofReal (fB s)) T := by
      have hatomν : volume.withDensity (fun s ↦ ENNReal.ofReal (fB s))
          {gerverStageTimes 3} = 0 := by
        rw [withDensity_apply _ (measurableSet_singleton _)]
        exact setLIntegral_measure_zero _ _ (by simp)
      intro T _ hTsub
      rw [measure_mono_null (Set.image_mono hTsub) hatom, measure_mono_null hTsub hatomν]
    -- gluing the closed stage and then the final open stage
    have hstep1 : ∀ T, MeasurableSet T →
        T ⊆ Set.Icc (gerverStageTimes 3) (gerverStageTimes 4) →
        (oppositeSurfaceData B).1 ((fun s : ℝ ↦ (s : Real.Angle)) '' T) =
          volume.withDensity (fun s ↦ ENNReal.ofReal (fB s)) T := by
      intro T hT hTsub
      refine measure_angleImage_eq_of_union (c := gerverStageTimes 3 - 1)
        (d := gerverStageTimes 5) (by linarith) (I := {gerverStageTimes 3})
        (J := Set.Ioc (gerverStageTimes 3) (gerverStageTimes 4)) ?_ ?_
        (measurableSet_singleton _) measurableSet_Ioc ?_ hagreeAtom hagree3 T hT ?_
      · intro x hx
        rw [Set.mem_singleton_iff] at hx
        exact ⟨by linarith, by linarith⟩
      · exact fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩
      · rw [Set.disjoint_singleton_left]
        simp
      · intro x hx
        rcases eq_or_lt_of_le (hTsub hx).1 with heq | hlt
        · exact Or.inl heq.symm
        · exact Or.inr ⟨hlt, (hTsub hx).2⟩
    have hstep2 : ∀ T, MeasurableSet T →
        T ⊆ Set.Ico (gerverStageTimes 3) (gerverStageTimes 5) →
        (oppositeSurfaceData B).1 ((fun s : ℝ ↦ (s : Real.Angle)) '' T) =
          volume.withDensity (fun s ↦ ENNReal.ofReal (fB s)) T := by
      intro T hT hTsub
      refine measure_angleImage_eq_of_union (c := gerverStageTimes 3 - 1)
        (d := gerverStageTimes 5) (by linarith)
        (I := Set.Icc (gerverStageTimes 3) (gerverStageTimes 4))
        (J := Set.Ioo (gerverStageTimes 4) (gerverStageTimes 5)) ?_ ?_
        measurableSet_Icc measurableSet_Ioo ?_ hstep1 hagree4 T hT ?_
      · exact fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩
      · exact fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩
      · rw [Set.disjoint_left]
        exact fun x hx hx' ↦ absurd hx'.1 (not_lt.2 hx.2)
      · intro x hx
        rcases le_or_gt x (gerverStageTimes 4) with h | h
        · exact Or.inl ⟨(hTsub hx).1, h⟩
        · exact Or.inr ⟨h, (hTsub hx).2⟩
    -- almost every parameter of the window lies in one of the two open stages
    have hae : ∀ᵐ t ∂volume.restrict (Set.Ico (gerverStageTimes 3) (gerverStageTimes 5)),
        t ∈ Set.Ioo (gerverStageTimes 3) (gerverStageTimes 4) ∪
          Set.Ioo (gerverStageTimes 4) (gerverStageTimes 5) := by
      refine ae_restrict_mem_of_countable_diff measurableSet_Ico
        ((Set.countable_singleton (gerverStageTimes 4)).insert (gerverStageTimes 3)) ?_
      rintro x ⟨hx, hx'⟩
      rcases eq_or_lt_of_le hx.1 with heq | hlt
      · exact Or.inl heq.symm
      · rcases lt_trichotomy x (gerverStageTimes 4) with h | h | h
        · exact absurd (Or.inl ⟨hlt, h⟩) hx'
        · exact Or.inr (Set.mem_singleton_iff.2 h)
        · exact absurd (Or.inr ⟨h, hx.2⟩) hx'
    have hsplit : Set.Ico (gerverStageTimes 3) (gerverStageTimes 5) =
        Set.Icc (gerverStageTimes 3) (gerverStageTimes 4) ∪
          Set.Ioo (gerverStageTimes 4) (gerverStageTimes 5) :=
      (Set.Icc_union_Ioo_eq_Ico h34.le h45).symm
    refine ⟨?_, ?_, ?_⟩
    · have h1 : IntegrableOn fB (Set.Icc (gerverStageTimes 3) (gerverStageTimes 4)) volume := by
        refine (ContinuousOn.integrableOn_compact isCompact_Icc hg3.continuousOn).congr ?_
        have hae3 : ∀ᵐ t ∂volume.restrict (Set.Icc (gerverStageTimes 3) (gerverStageTimes 4)),
            t ∈ Set.Ioo (gerverStageTimes 3) (gerverStageTimes 4) := by
          refine ae_restrict_mem_of_countable_diff measurableSet_Icc
            ((Set.countable_singleton (gerverStageTimes 4)).insert (gerverStageTimes 3)) ?_
          rintro x ⟨hx, hx'⟩
          rcases eq_or_lt_of_le hx.1 with heq | hlt
          · exact Or.inl heq.symm
          · rcases eq_or_lt_of_le hx.2 with heq2 | hlt2
            · exact Or.inr (Set.mem_singleton_iff.2 heq2)
            · exact absurd ⟨hlt, hlt2⟩ hx'
        filter_upwards [hae3] with t ht using (hfB3 t ht).symm
      have h2 : IntegrableOn fB (Set.Ioo (gerverStageTimes 4) (gerverStageTimes 5)) volume := by
        refine (((ContinuousOn.integrableOn_compact (isCompact_Icc
          (a := gerverStageTimes 4) (b := gerverStageTimes 5))
            hg4.continuousOn)).mono_set Set.Ioo_subset_Icc_self).congr ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht using (hfB4 t ht).symm
      rw [show Integrable fB (volume.restrict (Set.Ico (gerverStageTimes 3)
        (gerverStageTimes 5))) = IntegrableOn fB (Set.Ico (gerverStageTimes 3)
          (gerverStageTimes 5)) volume from rfl, hsplit]
      exact h1.union h2
    · filter_upwards [hae] with t ht
      rcases ht with ht | ht
      · rw [hfB3 t ht]
        exact hg3nn t ⟨ht.1, ht.2.le⟩
      · rw [hfB4 t ht]
        exact hg4nn t ⟨ht.1, ht.2.le⟩
    · rw [angularDensityMeasure]
      exact measure_restrict_eq_map_withDensity measurableSet_Ico hstep2
  · -- ### (3) the outer contact `C` against the moving normal on `(π/2, π]`
    have haeval : ∀ᵐ u ∂volume.restrict (Set.Ioc (Real.pi / 2) Real.pi),
        inner ℝ (-(deriv (fun s ↦ paperGerverContacts s 2) (u - Real.pi / 2)))
            (normalVector ((u - Real.pi / 2 : ℝ) : Real.Angle)) =
          (sden (u - Real.pi / 2) : ℝ) := by
      filter_upwards [ae_mem_openStage (Real.pi / 2) (S := Set.Ioc (Real.pi / 2) Real.pi)
        measurableSet_Ioc (fun u hu ↦ ⟨hu.1.le, by linarith [hu.2]⟩)] with u hu
      obtain ⟨j, hj⟩ := hu
      rw [(hstage j _ hj).2.deriv, neg_smul, neg_neg, real_inner_smul_left,
        inner_normalVector_self, mul_one]
    have hsint : Integrable (fun u ↦ ((sden (u - Real.pi / 2) : ℝ)))
        (volume.restrict (Set.Ioc (Real.pi / 2) Real.pi)) := by
      have hfin : IsFiniteMeasure (volume.restrict (Set.Ioc (Real.pi / 2) Real.pi)) := by
        refine ⟨?_⟩
        rw [Measure.restrict_apply_univ, Real.volume_Ioc]
        exact ENNReal.ofReal_lt_top
      refine Integrable.mono' (integrable_const M)
        ((hdens.2.1.coe_nnreal_real.comp (measurable_id.sub_const _)).aestronglyMeasurable) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      rw [Real.norm_eq_abs, abs_of_nonneg (sden _).coe_nonneg]
      exact (hM (u - Real.pi / 2) ⟨by linarith [hu.1], by linarith [hu.2]⟩).2
    refine ⟨hsint.congr (Filter.EventuallyEq.symm haeval), ?_, ?_⟩
    · filter_upwards [haeval] with u hu
      rw [hu]
      exact (sden _).coe_nonneg
    · have himg : (fun t : ℝ ↦ t + Real.pi / 2) '' Set.Ioc 0 (Real.pi / 2) =
          Set.Ioc (Real.pi / 2) Real.pi := by
        ext u
        simp only [Set.mem_image, Set.mem_Ioc]
        constructor
        · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
          exact ⟨by linarith, by linarith⟩
        · rintro ⟨h1, h2⟩
          exact ⟨u - Real.pi / 2, ⟨by linarith, by linarith⟩, by ring⟩
      have hcomp : (fun t : ℝ ↦ ((t + Real.pi / 2 : ℝ) : Real.Angle)) =
          (fun u : ℝ ↦ (u : Real.Angle)) ∘ (fun t : ℝ ↦ t + Real.pi / 2) := rfl
      rw [hdens.2.2.2, angularDensityMeasure, hcomp,
        ← Measure.map_map (g := fun u : ℝ ↦ (u : Real.Angle))
          (f := fun t : ℝ ↦ t + Real.pi / 2) Real.Angle.continuous_coe.measurable (by fun_prop),
        map_add_right_restrict_withDensity (Real.pi / 2), himg]
      congr 1
      refine withDensity_congr_ae ?_
      filter_upwards [haeval] with u hu
      rw [hu, ENNReal.ofReal_coe_nnreal]
  · -- ### (4) the inner contact `D` against the moving normal on `(π/2 + t₀, π/2 + t₂]`
    obtain ⟨fD, hfDdef⟩ : ∃ f : ℝ → ℝ, f = fun t ↦ inner ℝ
        (deriv (fun s ↦ paperGerverContacts s 3) (t - Real.pi / 2))
        (normalVector ((t - Real.pi / 2 : ℝ) : Real.Angle)) := ⟨_, rfl⟩
    rw [← hfDdef]
    obtain ⟨F0, g0, hF0, hg0, hg0nn, hFeq0⟩ :=
      exists_branch_paperGerverContacts_three (i := 0) (Or.inl rfl)
    obtain ⟨F1, g1, hF1, hg1, hg1nn, hFeq1⟩ :=
      exists_branch_paperGerverContacts_three (i := 1) (Or.inr rfl)
    -- the stage data with the stage times spelled out, so that `linarith` sees them
    have hg0nn' : ∀ t ∈ Set.Ioc (gerverStageTimes 0) (gerverStageTimes 1), 0 ≤ g0 t := hg0nn
    have hFeq0' : ∀ t ∈ Set.Icc (gerverStageTimes 0) (gerverStageTimes 1),
        paperGerverContacts t 3 = F0 t := hFeq0
    have hg1nn' : ∀ t ∈ Set.Ioc (gerverStageTimes 1) (gerverStageTimes 2), 0 ≤ g1 t := hg1nn
    have hFeq1' : ∀ t ∈ Set.Icc (gerverStageTimes 1) (gerverStageTimes 2),
        paperGerverContacts t 3 = F1 t := hFeq1
    -- reparametrising the quarter-turn shift turns the normal speed into a tangent speed
    have hshift : ∀ (F : ℝ → Point) (g : ℝ → ℝ),
        (∀ s, HasDerivAt F (g s • normalVector (s : Real.Angle)) s) →
        ∀ u : ℝ, HasDerivAt (fun v : ℝ ↦ F (v - Real.pi / 2))
          (-(g (u - Real.pi / 2)) • tangentVector (u : Real.Angle)) u := by
      intro F g hF u
      have h := (hF (u - Real.pi / 2)).scomp u ((hasDerivAt_id u).sub_const (Real.pi / 2))
      have hv : tangentVector (u : Real.Angle) =
          -normalVector ((u - Real.pi / 2 : ℝ) : Real.Angle) := by
        have h2 := tangentVector_add_pi_div_two (u - Real.pi / 2)
        rw [show u - Real.pi / 2 + Real.pi / 2 = u from by ring] at h2
        exact h2
      rw [hv]
      refine h.congr_deriv ?_
      module
    -- the positive vertex of `D` at normal `π + u` is the inner contact
    have hvD : ∀ u ∈ Set.Ioc (Real.pi / 2 + gerverStageTimes 0)
        (Real.pi / 2 + gerverStageTimes 2),
        (edgeVertices D ((Real.pi + u : ℝ) : Real.Angle)).1 =
          paperGerverContacts (u - Real.pi / 2) 3 := by
      intro u hu
      rw [show ((Real.pi + u : ℝ) : Real.Angle) =
        ((3 * Real.pi / 2 + (u - Real.pi / 2) : ℝ) : Real.Angle) from by congr 1; ring]
      rcases eq_or_lt_of_le hu.2 with heq | hlt
      · rw [show u - Real.pi / 2 = gerverStageTimes 2 from by linarith, htailD2]
      · rw [htailD (u - Real.pi / 2) ⟨by linarith [hu.1], by linarith⟩]
    -- the target density is the shifted branch speed inside each of the two open stages
    have hfD0 : ∀ u ∈ Set.Ioo (Real.pi / 2 + gerverStageTimes 0)
        (Real.pi / 2 + gerverStageTimes 1), fD u = g0 (u - Real.pi / 2) := by
      intro u hu
      simp only [hfDdef]
      rw [(hasDerivAt_of_eqOn_stage hF0 hFeq0 (show u - Real.pi / 2 ∈
        Set.Ioo (gerverStageTimes 0) (gerverStageTimes 1) from
          ⟨by linarith [hu.1], by linarith [hu.2]⟩)).deriv, real_inner_smul_left,
        inner_normalVector_self, mul_one]
    have hfD1 : ∀ u ∈ Set.Ioo (Real.pi / 2 + gerverStageTimes 1)
        (Real.pi / 2 + gerverStageTimes 2), fD u = g1 (u - Real.pi / 2) := by
      intro u hu
      simp only [hfDdef]
      rw [(hasDerivAt_of_eqOn_stage hF1 hFeq1 (show u - Real.pi / 2 ∈
        Set.Ioo (gerverStageTimes 1) (gerverStageTimes 2) from
          ⟨by linarith [hu.1], by linarith [hu.2]⟩)).deriv, real_inner_smul_left,
        inner_normalVector_self, mul_one]
    -- the two stage windows
    have hagree0 : ∀ T, MeasurableSet T →
        T ⊆ Set.Ioc (Real.pi / 2 + gerverStageTimes 0) (Real.pi / 2 + gerverStageTimes 1) →
        (oppositeSurfaceData D).1 ((fun s : ℝ ↦ (s : Real.Angle)) '' T) =
          volume.withDensity (fun s ↦ ENNReal.ofReal (fD s)) T := by
      intro T hT hTsub
      refine oppositeSurfaceData_angleImage_eq_withDensity_of_openLeft D (by linarith)
        (by linarith) (fun v ↦ F0 (v - Real.pi / 2)) fD (fun u ↦ g0 (u - Real.pi / 2))
        (hshift F0 g0 hF0) (hg0.comp (continuous_id.sub continuous_const))
        (fun s hs ↦ hg0nn' _ ⟨by linarith [hs.1], by linarith [hs.2]⟩) hfD0 ?_ hT hTsub
      exact fun s hs ↦ (hvD s ⟨hs.1, by linarith [hs.2]⟩).trans
        (hFeq0' _ ⟨by linarith [hs.1], by linarith [hs.2]⟩)
    have hagree1 : ∀ T, MeasurableSet T →
        T ⊆ Set.Ioc (Real.pi / 2 + gerverStageTimes 1) (Real.pi / 2 + gerverStageTimes 2) →
        (oppositeSurfaceData D).1 ((fun s : ℝ ↦ (s : Real.Angle)) '' T) =
          volume.withDensity (fun s ↦ ENNReal.ofReal (fD s)) T := by
      intro T hT hTsub
      refine oppositeSurfaceData_angleImage_eq_withDensity D (by linarith) (by linarith)
        (fun v ↦ F1 (v - Real.pi / 2)) fD (fun u ↦ g1 (u - Real.pi / 2)) (hshift F1 g1 hF1)
        (hg1.comp (continuous_id.sub continuous_const))
        (fun s hs ↦ hg1nn' _ ⟨by linarith [hs.1], by linarith [hs.2]⟩) hfD1 ?_ hT hTsub
      exact fun s hs ↦ (hvD s ⟨by linarith [hs.1], by linarith [hs.2]⟩).trans
        (hFeq1' _ ⟨by linarith [hs.1], by linarith [hs.2]⟩)
    have hstep : ∀ T, MeasurableSet T →
        T ⊆ Set.Ioc (Real.pi / 2 + gerverStageTimes 0) (Real.pi / 2 + gerverStageTimes 2) →
        (oppositeSurfaceData D).1 ((fun s : ℝ ↦ (s : Real.Angle)) '' T) =
          volume.withDensity (fun s ↦ ENNReal.ofReal (fD s)) T := by
      intro T hT hTsub
      refine measure_angleImage_eq_of_union (c := Real.pi / 2 + gerverStageTimes 0)
        (d := Real.pi / 2 + gerverStageTimes 2) (by linarith)
        (I := Set.Ioc (Real.pi / 2 + gerverStageTimes 0) (Real.pi / 2 + gerverStageTimes 1))
        (J := Set.Ioc (Real.pi / 2 + gerverStageTimes 1) (Real.pi / 2 + gerverStageTimes 2)) ?_ ?_
        measurableSet_Ioc measurableSet_Ioc ?_ hagree0 hagree1 T hT ?_
      · exact fun x hx ↦ ⟨hx.1, by linarith [hx.2]⟩
      · exact fun x hx ↦ ⟨by linarith [hx.1], hx.2⟩
      · rw [Set.disjoint_left]
        exact fun x hx hx' ↦ absurd hx'.1 (not_lt.2 hx.2)
      · intro x hx
        rcases le_or_gt x (Real.pi / 2 + gerverStageTimes 1) with h | h
        · exact Or.inl ⟨(hTsub hx).1, h⟩
        · exact Or.inr ⟨h, (hTsub hx).2⟩
    have hsplit : Set.Ioc (Real.pi / 2 + gerverStageTimes 0) (Real.pi / 2 + gerverStageTimes 2) =
        Set.Ioc (Real.pi / 2 + gerverStageTimes 0) (Real.pi / 2 + gerverStageTimes 1) ∪
          Set.Ioc (Real.pi / 2 + gerverStageTimes 1) (Real.pi / 2 + gerverStageTimes 2) :=
      (Set.Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith)).symm
    have hae : ∀ᵐ u ∂volume.restrict (Set.Ioc (Real.pi / 2 + gerverStageTimes 0)
        (Real.pi / 2 + gerverStageTimes 2)),
        u ∈ Set.Ioo (Real.pi / 2 + gerverStageTimes 0) (Real.pi / 2 + gerverStageTimes 1) ∪
          Set.Ioo (Real.pi / 2 + gerverStageTimes 1) (Real.pi / 2 + gerverStageTimes 2) := by
      refine ae_restrict_mem_of_countable_diff measurableSet_Ioc
        ((Set.countable_singleton (Real.pi / 2 + gerverStageTimes 2)).insert
          (Real.pi / 2 + gerverStageTimes 1)) ?_
      rintro x ⟨hx, hx'⟩
      rcases lt_trichotomy x (Real.pi / 2 + gerverStageTimes 1) with h | h | h
      · exact absurd (Or.inl ⟨hx.1, h⟩) hx'
      · exact Or.inl h
      · rcases eq_or_lt_of_le hx.2 with heq | hlt
        · exact Or.inr (Set.mem_singleton_iff.2 heq)
        · exact absurd (Or.inr ⟨h, hlt⟩) hx'
    refine ⟨?_, ?_, ?_⟩
    · have hae01 : ∀ a b : ℝ, ∀ᵐ u ∂volume.restrict (Set.Ioc a b),
          u ∈ Set.Ioo a b := by
        intro a b
        refine ae_restrict_mem_of_countable_diff measurableSet_Ioc
          (Set.countable_singleton b) ?_
        rintro x ⟨hx, hx'⟩
        exact le_antisymm hx.2 (not_lt.1 fun h ↦ hx' ⟨hx.1, h⟩)
      have hint0 : IntegrableOn fD (Set.Ioc (Real.pi / 2 + gerverStageTimes 0)
          (Real.pi / 2 + gerverStageTimes 1)) volume := by
        have hc0 : Continuous fun u : ℝ ↦ g0 (u - Real.pi / 2) :=
          hg0.comp (continuous_id.sub continuous_const)
        refine (((ContinuousOn.integrableOn_compact (isCompact_Icc
          (a := Real.pi / 2 + gerverStageTimes 0) (b := Real.pi / 2 + gerverStageTimes 1))
            hc0.continuousOn)).mono_set Set.Ioc_subset_Icc_self).congr ?_
        filter_upwards [hae01 _ _] with u hu using (hfD0 u hu).symm
      have hint1 : IntegrableOn fD (Set.Ioc (Real.pi / 2 + gerverStageTimes 1)
          (Real.pi / 2 + gerverStageTimes 2)) volume := by
        have hc1 : Continuous fun u : ℝ ↦ g1 (u - Real.pi / 2) :=
          hg1.comp (continuous_id.sub continuous_const)
        refine (((ContinuousOn.integrableOn_compact (isCompact_Icc
          (a := Real.pi / 2 + gerverStageTimes 1) (b := Real.pi / 2 + gerverStageTimes 2))
            hc1.continuousOn)).mono_set Set.Ioc_subset_Icc_self).congr ?_
        filter_upwards [hae01 _ _] with u hu using (hfD1 u hu).symm
      rw [show Integrable fD (volume.restrict (Set.Ioc (Real.pi / 2 + gerverStageTimes 0)
        (Real.pi / 2 + gerverStageTimes 2))) = IntegrableOn fD
          (Set.Ioc (Real.pi / 2 + gerverStageTimes 0)
            (Real.pi / 2 + gerverStageTimes 2)) volume from rfl, hsplit]
      exact hint0.union hint1
    · filter_upwards [hae] with u hu
      rcases hu with hu | hu
      · rw [hfD0 u hu]
        exact hg0nn' _ ⟨by linarith [hu.1], by linarith [hu.2]⟩
      · rw [hfD1 u hu]
        exact hg1nn' _ ⟨by linarith [hu.1], by linarith [hu.2]⟩
    · rw [angularDensityMeasure]
      exact measure_restrict_eq_map_withDensity measurableSet_Ioc hstep

end MovingSofa
