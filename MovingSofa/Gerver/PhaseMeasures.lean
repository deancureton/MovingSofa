import MovingSofa.Cap.CornerMeasure
import MovingSofa.Gerver.Partition
import MovingSofa.Gerver.MeasureTranslation
import MovingSofa.Gerver.ODEs

/-!
# The eight phase identities of Gerver's cap

The ten Gerver phase intervals cut the angular window `[0, π]` at the five stage times and at
their reflections.  On each of them the surface-area measure of the cap `K = C(G)` of Gerver's
sofa is one of: zero, the inner-corner measure `ι_K`, the opposite surface measure of one of the
two tail bodies, or a sum of the last two (`gerver_phaseMeasures`).

Every clause is proved set-wise.  The translated-measure proposition `gerver_measureTranslation`
presents the surface measure of the cap and the two opposite tail measures as angular densities
on the two half-windows, so each of them gives the angular image of a measurable subset of a
phase interval the Lebesgue integral of the corresponding contact derivative
(`HasAngularDensity.angleImage_eq_setLIntegral`), and the corner measure does the same with its
own density (`capCornerAngleMeasure_angleImage_eq_setLIntegral`).  The five stagewise contact
equations `gerver_stageODEs` identify those densities on the interior of each stage, which is
almost all of it, and `Real.Angle.measure_restrict_image_congr_of_ae_eq` turns an
almost-everywhere identity of densities into an equality of the restricted measures.  No atom
computation at the included stage endpoints is needed: a single parameter is Lebesgue-null and
the four measures are only ever evaluated through their densities.
-/

noncomputable section

open MeasureTheory

namespace MovingSofa

def gerverPhaseAngles (j : Fin 10) : Set Real.Angle :=
  (fun t : ℝ ↦ (t : Real.Angle)) '' gerverPhaseIntervals j

def GerverPhaseMeasureIdentities (K : SpecialCapSpace) (B D : ConvexBody Point) : Prop :=
  (surfaceAreaMeasure K.val.val).restrict (gerverPhaseAngles 0) = 0 ∧
  (surfaceAreaMeasure K.val.val).restrict (gerverPhaseAngles 1 ∪ gerverPhaseAngles 2) =
    (capCornerAngleMeasure K).restrict (gerverPhaseAngles 1 ∪ gerverPhaseAngles 2) ∧
  (surfaceAreaMeasure K.val.val).restrict (gerverPhaseAngles 3) =
    ((oppositeSurfaceData B).1 + capCornerAngleMeasure K).restrict (gerverPhaseAngles 3) ∧
  (surfaceAreaMeasure K.val.val).restrict (gerverPhaseAngles 4) =
    (oppositeSurfaceData B).1.restrict (gerverPhaseAngles 4) ∧
  (surfaceAreaMeasure K.val.val).restrict (gerverPhaseAngles 5) =
    (oppositeSurfaceData D).1.restrict (gerverPhaseAngles 5) ∧
  (surfaceAreaMeasure K.val.val).restrict (gerverPhaseAngles 6) =
    ((oppositeSurfaceData D).1 + capCornerAngleMeasure K).restrict (gerverPhaseAngles 6) ∧
  (surfaceAreaMeasure K.val.val).restrict (gerverPhaseAngles 7 ∪ gerverPhaseAngles 8) =
    (capCornerAngleMeasure K).restrict (gerverPhaseAngles 7 ∪ gerverPhaseAngles 8) ∧
  (surfaceAreaMeasure K.val.val).restrict (gerverPhaseAngles 9) = 0

/-! ### The corner density of the cap of Gerver's sofa

On each of the two open quarter turns the inner corner of the cap is the direct Gerver path
(`derivWithin_capInnerCorner_eq_deriv_paperGerverPath`), so the two branches of
`capCornerDensity` are the two velocity components `β` and `-α` of that path. -/

/-- On the first open quarter turn the corner density of the cap of Gerver's sofa is the
tangential velocity component of the direct Gerver path. -/
theorem capCornerDensity_eq_velocity_tangential (K : SpecialCapSpace)
    (hK : (K.val.val : Set Point) = capOfSofa paperGerverSofa (Real.pi / 2)) {s : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    capCornerDensity K s = (paperGerverVelocityComponents s).2 := by
  simp only [capCornerDensity]
  split_ifs with h1 h2
  · simp only [capVelocityCoefficients, paperGerverVelocityComponents,
      derivWithin_capInnerCorner_eq_deriv_paperGerverPath K.val hK hs]
  · exact absurd ⟨hs.1, hs.2.le⟩ h1
  · exact absurd ⟨hs.1, hs.2.le⟩ h1

/-- On the second open quarter turn the corner density of the cap of Gerver's sofa is minus the
normal velocity component of the direct Gerver path, at the parameter shifted by a quarter
turn. -/
theorem capCornerDensity_eq_neg_velocity_normal (K : SpecialCapSpace)
    (hK : (K.val.val : Set Point) = capOfSofa paperGerverSofa (Real.pi / 2)) {s : ℝ}
    (hs : s ∈ Set.Ioo (Real.pi / 2) Real.pi) :
    capCornerDensity K s = -(paperGerverVelocityComponents (s - Real.pi / 2)).1 := by
  have hs' : s - Real.pi / 2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  simp only [capCornerDensity]
  split_ifs with h1 h2
  · exact absurd h1.2 (not_le.2 hs.1)
  · simp only [capVelocityCoefficients, paperGerverVelocityComponents,
      derivWithin_capInnerCorner_eq_deriv_paperGerverPath K.val hK hs']
  · exact absurd ⟨hs.1, hs.2.le⟩ h2

theorem gerver_phaseMeasures (K : SpecialCapSpace) (B D : ConvexBody Point)
    (hK : (K.val.val : Set Point) = capOfSofa paperGerverSofa (Real.pi / 2))
    (hB : (B : Set Point) = (canonicalTailSets K).1)
    (hD : (D : Set Point) = (canonicalTailSets K).2) :
    GerverPhaseMeasureIdentities K B D := by
  -- ### The six stage endpoints, written out
  have hmono := gerverStageTimes_strictMono
  have h01 := hmono (show (0 : Fin 6) < 1 by decide)
  have h12 := hmono (show (1 : Fin 6) < 2 by decide)
  have h23 := hmono (show (2 : Fin 6) < 3 by decide)
  have h34 := hmono (show (3 : Fin 6) < 4 by decide)
  have h45 := hmono (show (4 : Fin 6) < 5 by decide)
  simp only [gerverStageTimes, Matrix.cons_val] at h01 h12 h23 h34 h45
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hturn : Real.pi ≤ -1 + 2 * Real.pi := by linarith
  -- ### The five closed stage intervals
  have hI0 : gerverStageIntervals 0 = Set.Icc 0 GerversSofa.φ := by
    simp [gerverStageIntervals, gerverStageTimes]
  have hI1 : gerverStageIntervals 1 = Set.Icc GerversSofa.φ GerversSofa.θ := by
    simp [gerverStageIntervals, gerverStageTimes]
  have hI2 : gerverStageIntervals 2 =
      Set.Icc GerversSofa.θ (Real.pi / 2 - GerversSofa.θ) := by
    simp [gerverStageIntervals, gerverStageTimes]
  have hI3 : gerverStageIntervals 3 =
      Set.Icc (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2 - GerversSofa.φ) := by
    simp [gerverStageIntervals, gerverStageTimes]
  have hI4 : gerverStageIntervals 4 =
      Set.Icc (Real.pi / 2 - GerversSofa.φ) (Real.pi / 2) := by
    simp [gerverStageIntervals, gerverStageTimes]
  -- ### The ten phase intervals
  have hJ0 : gerverPhaseIntervals 0 = Set.Ico 0 GerversSofa.φ :=
    gerverPhaseIntervals_explicit 0
  have hJ1 : gerverPhaseIntervals 1 = Set.Ico GerversSofa.φ GerversSofa.θ :=
    gerverPhaseIntervals_explicit 1
  have hJ2 : gerverPhaseIntervals 2 =
      Set.Ico GerversSofa.θ (Real.pi / 2 - GerversSofa.θ) :=
    gerverPhaseIntervals_explicit 2
  have hJ3 : gerverPhaseIntervals 3 =
      Set.Ico (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2 - GerversSofa.φ) :=
    gerverPhaseIntervals_explicit 3
  have hJ4 : gerverPhaseIntervals 4 =
      Set.Ico (Real.pi / 2 - GerversSofa.φ) (Real.pi / 2) :=
    gerverPhaseIntervals_explicit 4
  have hJ5 : gerverPhaseIntervals 5 =
      Set.Ioc (Real.pi / 2) (Real.pi / 2 + GerversSofa.φ) :=
    gerverPhaseIntervals_explicit 5
  have hJ6 : gerverPhaseIntervals 6 =
      Set.Ioc (Real.pi / 2 + GerversSofa.φ) (Real.pi / 2 + GerversSofa.θ) :=
    gerverPhaseIntervals_explicit 6
  have hJ7 : gerverPhaseIntervals 7 =
      Set.Ioc (Real.pi / 2 + GerversSofa.θ) (Real.pi - GerversSofa.θ) :=
    gerverPhaseIntervals_explicit 7
  have hJ8 : gerverPhaseIntervals 8 =
      Set.Ioc (Real.pi - GerversSofa.θ) (Real.pi - GerversSofa.φ) :=
    gerverPhaseIntervals_explicit 8
  have hJ9 : gerverPhaseIntervals 9 = Set.Ioc (Real.pi - GerversSofa.φ) Real.pi :=
    gerverPhaseIntervals_explicit 9
  -- ### The four contact densities of the translated-measure proposition
  have hd := gerver_measureTranslation K B D hK hB hD
  obtain ⟨fA, hfAdef⟩ : ∃ f : ℝ → ℝ, f = fun t ↦ inner ℝ
      (deriv (fun s ↦ paperGerverContacts s 0) t) (tangentVector (t : Real.Angle)) := ⟨_, rfl⟩
  obtain ⟨fB, hfBdef⟩ : ∃ f : ℝ → ℝ, f = fun t ↦ inner ℝ
      (-(deriv (fun s ↦ paperGerverContacts s 1) t))
      (tangentVector (t : Real.Angle)) := ⟨_, rfl⟩
  obtain ⟨fC, hfCdef⟩ : ∃ f : ℝ → ℝ, f = fun t ↦ inner ℝ
      (-(deriv (fun s ↦ paperGerverContacts s 2) (t - Real.pi / 2)))
      (normalVector ((t - Real.pi / 2 : ℝ) : Real.Angle)) := ⟨_, rfl⟩
  obtain ⟨fD, hfDdef⟩ : ∃ f : ℝ → ℝ, f = fun t ↦ inner ℝ
      (deriv (fun s ↦ paperGerverContacts s 3) (t - Real.pi / 2))
      (normalVector ((t - Real.pi / 2 : ℝ) : Real.Angle)) := ⟨_, rfl⟩
  rw [← hfAdef, ← hfBdef, ← hfCdef, ← hfDdef,
    show Set.Ico (gerverStageTimes 3) (gerverStageTimes 5) =
      Set.Ico (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2) from by simp [gerverStageTimes],
    show Set.Ioc (Real.pi / 2 + gerverStageTimes 0) (Real.pi / 2 + gerverStageTimes 2) =
      Set.Ioc (Real.pi / 2) (Real.pi / 2 + GerversSofa.θ) from by simp [gerverStageTimes]] at hd
  obtain ⟨hdA, hdB, hdC, hdD⟩ := hd
  -- ### The four density windows sit inside a single turn
  have hsubA : Set.Ico (0 : ℝ) (Real.pi / 2) ⊆ Set.Ioc (-1 : ℝ) Real.pi :=
    fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hsubB : Set.Ico (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2) ⊆
      Set.Ioc (-1 : ℝ) Real.pi := fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hsubC : Set.Ioc (Real.pi / 2) Real.pi ⊆ Set.Ioc (-1 : ℝ) Real.pi :=
    fun x hx ↦ ⟨by linarith [hx.1], hx.2⟩
  have hsubD : Set.Ioc (Real.pi / 2) (Real.pi / 2 + GerversSofa.θ) ⊆
      Set.Ioc (-1 : ℝ) Real.pi := fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩
  -- ### Inside an open stage the stagewise derivatives are the global ones
  have hconv : ∀ (i : Fin 5) (a b t : ℝ), gerverStageIntervals i = Set.Icc a b →
      a < t → t < b →
      gerverStageContactDerivatives i t 0 = fA t ∧
      gerverStageContactDerivatives i t 1 = -fB t ∧
      gerverStageContactDerivatives i t 2 = fC (t + Real.pi / 2) ∧
      gerverStageContactDerivatives i t 3 = fD (t + Real.pi / 2) := by
    intro i a b t hI ha hb
    have hn : gerverStageIntervals i ∈ nhds t := by rw [hI]; exact Icc_mem_nhds ha hb
    have e : ∀ k : Fin 4,
        derivWithin (fun s ↦ paperGerverContacts s k) (gerverStageIntervals i) t =
          deriv (fun s ↦ paperGerverContacts s k) t := fun _ ↦ derivWithin_of_mem_nhds hn
    refine ⟨?_, ?_, ?_, ?_⟩
    · show inner ℝ (derivWithin (fun s ↦ paperGerverContacts s 0) (gerverStageIntervals i) t)
        (tangentVector (t : Real.Angle)) = fA t
      rw [e 0, hfAdef]
    · show inner ℝ (derivWithin (fun s ↦ paperGerverContacts s 1) (gerverStageIntervals i) t)
        (tangentVector (t : Real.Angle)) = -fB t
      rw [e 1, hfBdef]
      simp [inner_neg_left]
    · show inner ℝ (-derivWithin (fun s ↦ paperGerverContacts s 2) (gerverStageIntervals i) t)
        (normalVector (t : Real.Angle)) = fC (t + Real.pi / 2)
      rw [e 2, hfCdef]
      simp
    · show inner ℝ (derivWithin (fun s ↦ paperGerverContacts s 3) (gerverStageIntervals i) t)
        (normalVector (t : Real.Angle)) = fD (t + Real.pi / 2)
      rw [e 3, hfDdef]
      simp
  -- ### The five stage coefficient identities, at interior parameters
  have hode : ∀ (i : Fin 5) (a b t : ℝ), gerverStageIntervals i = Set.Icc a b →
      a < t → t < b →
      (gerverStageContactDerivatives i t 0, gerverStageContactDerivatives i t 2) =
        ![(0, gerverStageContactDerivatives i t 3),
          ((paperGerverVelocityComponents t).2,
            gerverStageContactDerivatives i t 3 - (paperGerverVelocityComponents t).1),
          ((paperGerverVelocityComponents t).2, -(paperGerverVelocityComponents t).1),
          (-gerverStageContactDerivatives i t 1 + (paperGerverVelocityComponents t).2,
            -(paperGerverVelocityComponents t).1),
          (-gerverStageContactDerivatives i t 1, 0)] i :=
    fun i a b t hI ha hb ↦ gerver_stageODEs i t (by rw [hI]; exact ⟨ha.le, hb.le⟩)
  have hs0 : ∀ t ∈ Set.Ioo (0 : ℝ) GerversSofa.φ,
      fA t = 0 ∧ fC (t + Real.pi / 2) = fD (t + Real.pi / 2) := by
    intro t ht
    obtain ⟨e0, -, e2, e3⟩ := hconv 0 _ _ t hI0 ht.1 ht.2
    have h := hode 0 _ _ t hI0 ht.1 ht.2
    simp only [Matrix.cons_val, Prod.mk.injEq] at h
    exact ⟨e0.symm.trans h.1, e2.symm.trans (h.2.trans e3)⟩
  have hs1 : ∀ t ∈ Set.Ioo GerversSofa.φ GerversSofa.θ,
      fA t = (paperGerverVelocityComponents t).2 ∧
      fC (t + Real.pi / 2) =
        fD (t + Real.pi / 2) - (paperGerverVelocityComponents t).1 := by
    intro t ht
    obtain ⟨e0, -, e2, e3⟩ := hconv 1 _ _ t hI1 ht.1 ht.2
    have h := hode 1 _ _ t hI1 ht.1 ht.2
    simp only [Matrix.cons_val, Prod.mk.injEq] at h
    exact ⟨e0.symm.trans h.1, e2.symm.trans (h.2.trans (by rw [e3]))⟩
  have hs2 : ∀ t ∈ Set.Ioo GerversSofa.θ (Real.pi / 2 - GerversSofa.θ),
      fA t = (paperGerverVelocityComponents t).2 ∧
      fC (t + Real.pi / 2) = -(paperGerverVelocityComponents t).1 := by
    intro t ht
    obtain ⟨e0, -, e2, -⟩ := hconv 2 _ _ t hI2 ht.1 ht.2
    have h := hode 2 _ _ t hI2 ht.1 ht.2
    simp only [Matrix.cons_val, Prod.mk.injEq] at h
    exact ⟨e0.symm.trans h.1, e2.symm.trans h.2⟩
  have hs3 : ∀ t ∈ Set.Ioo (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2 - GerversSofa.φ),
      fA t = fB t + (paperGerverVelocityComponents t).2 ∧
      fC (t + Real.pi / 2) = -(paperGerverVelocityComponents t).1 := by
    intro t ht
    obtain ⟨e0, e1, e2, -⟩ := hconv 3 _ _ t hI3 ht.1 ht.2
    have h := hode 3 _ _ t hI3 ht.1 ht.2
    simp only [Matrix.cons_val, Prod.mk.injEq] at h
    refine ⟨e0.symm.trans (h.1.trans ?_), e2.symm.trans h.2⟩
    rw [e1, neg_neg]
  have hs4 : ∀ t ∈ Set.Ioo (Real.pi / 2 - GerversSofa.φ) (Real.pi / 2),
      fA t = fB t ∧ fC (t + Real.pi / 2) = 0 := by
    intro t ht
    obtain ⟨e0, e1, e2, -⟩ := hconv 4 _ _ t hI4 ht.1 ht.2
    have h := hode 4 _ _ t hI4 ht.1 ht.2
    simp only [Matrix.cons_val, Prod.mk.injEq] at h
    refine ⟨e0.symm.trans (h.1.trans ?_), e2.symm.trans h.2⟩
    rw [e1, neg_neg]
  -- ### The strict interior signs of the injectivity condition of the given special cap
  have hβ : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      0 ≤ (paperGerverVelocityComponents t).2 := by
    intro t ht
    have h := (K.2.1.2.2 t ht).2
    rw [derivWithin_capInnerCorner_eq_deriv_paperGerverPath K.val hK ht] at h
    exact h.le
  have hα : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      0 ≤ -(paperGerverVelocityComponents t).1 := by
    intro t ht
    have h := (K.2.1.2.2 t ht).1
    rw [derivWithin_capInnerCorner_eq_deriv_paperGerverPath K.val hK ht] at h
    exact neg_nonneg.2 h.le
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- ### (1) the surface measure vanishes on the first phase
    have hsub : Set.Ico (0 : ℝ) GerversSofa.φ ⊆ Set.Ico (0 : ℝ) (Real.pi / 2) :=
      fun x hx ↦ ⟨hx.1, by linarith [hx.2]⟩
    simp only [gerverPhaseAngles, hJ0]
    rw [Measure.restrict_eq_zero,
      hdA.angleImage_eq_setLIntegral hturn hsubA measurableSet_Ico hsub]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [ae_restrict_Ico_mem_Ioo (μ := volume) 0 GerversSofa.φ] with t ht
    rw [(hs0 t ht).1, ENNReal.ofReal_zero]
  · -- ### (2) the surface measure is the corner measure on the second and third phases
    have hsub : Set.Ico GerversSofa.φ (Real.pi / 2 - GerversSofa.θ) ⊆
        Set.Ico (0 : ℝ) (Real.pi / 2) :=
      fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hsubI : Set.Ico GerversSofa.φ (Real.pi / 2 - GerversSofa.θ) ⊆
        Set.Icc (0 : ℝ) Real.pi :=
      fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hU : gerverPhaseAngles 1 ∪ gerverPhaseAngles 2 =
        (fun s : ℝ ↦ (s : Real.Angle)) ''
          Set.Ico GerversSofa.φ (Real.pi / 2 - GerversSofa.θ) := by
      simp only [gerverPhaseAngles, hJ1, hJ2, ← Set.image_union,
        Set.Ico_union_Ico_eq_Ico h12.le h23.le]
    rw [hU]
    refine Real.Angle.measure_restrict_image_congr_of_ae_eq measurableSet_Ico
      (fun T hT hTsub ↦ hdA.angleImage_eq_setLIntegral hturn hsubA hT (hTsub.trans hsub))
      (fun T hT hTsub ↦ capCornerAngleMeasure_angleImage_eq_setLIntegral K hT
        (hTsub.trans hsubI)) ?_
    filter_upwards [ae_restrict_Ico_mem_Ioo_union_Ioo (μ := volume) GerversSofa.φ GerversSofa.θ
      (Real.pi / 2 - GerversSofa.θ)] with t ht
    rcases ht with ht | ht
    · rw [(hs1 t ht).1,
        capCornerDensity_eq_velocity_tangential K hK ⟨by linarith [ht.1], by linarith [ht.2]⟩]
    · rw [(hs2 t ht).1,
        capCornerDensity_eq_velocity_tangential K hK ⟨by linarith [ht.1], by linarith [ht.2]⟩]
  · -- ### (3) the surface measure is the right tail plus the corner measure on phase four
    have hsub : Set.Ico (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2 - GerversSofa.φ) ⊆
        Set.Ico (0 : ℝ) (Real.pi / 2) :=
      fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hsubB' : Set.Ico (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2 - GerversSofa.φ) ⊆
        Set.Ico (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2) :=
      fun x hx ↦ ⟨hx.1, by linarith [hx.2]⟩
    have hsubI : Set.Ico (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2 - GerversSofa.φ) ⊆
        Set.Icc (0 : ℝ) Real.pi :=
      fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hsubO : Set.Ico (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2 - GerversSofa.φ) ⊆
        Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hcorner : ∀ T, MeasurableSet T →
        T ⊆ Set.Ico (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2 - GerversSofa.φ) →
        capCornerAngleMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' T) =
          ∫⁻ t in T, ENNReal.ofReal ((paperGerverVelocityComponents t).2) ∂volume := by
      intro T hT hTsub
      rw [capCornerAngleMeasure_angleImage_eq_setLIntegral K hT (hTsub.trans hsubI)]
      exact setLIntegral_congr_fun hT fun t ht ↦ by
        rw [capCornerDensity_eq_velocity_tangential K hK (hsubO (hTsub ht))]
    have hf0 : ∀ᵐ t ∂volume.restrict
        (Set.Ico (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2 - GerversSofa.φ)), 0 ≤ fB t :=
      ae_restrict_of_ae_restrict_of_subset hsubB' hdB.2.1
    have hg0 : ∀ᵐ t ∂volume.restrict
        (Set.Ico (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2 - GerversSofa.φ)),
        0 ≤ (paperGerverVelocityComponents t).2 := by
      filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht using hβ t (hsubO ht)
    have hsum : ∀ᵐ t ∂volume.restrict
        (Set.Ico (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2 - GerversSofa.φ)),
        fA t = fB t + (paperGerverVelocityComponents t).2 := by
      filter_upwards [ae_restrict_Ico_mem_Ioo (μ := volume) (Real.pi / 2 - GerversSofa.θ)
        (Real.pi / 2 - GerversSofa.φ)] with t ht using (hs3 t ht).1
    simp only [gerverPhaseAngles, hJ3]
    exact Real.Angle.measure_restrict_image_congr_add measurableSet_Ico
      (fun T hT hTsub ↦ hdA.angleImage_eq_setLIntegral hturn hsubA hT (hTsub.trans hsub))
      (fun T hT hTsub ↦ hdB.angleImage_eq_setLIntegral hturn hsubB hT (hTsub.trans hsubB'))
      hcorner (hdB.1.aemeasurable.mono_measure (Measure.restrict_mono hsubB' le_rfl))
      hf0 hg0 hsum
  · -- ### (4) the surface measure is the right tail on phase five
    have hsub : Set.Ico (Real.pi / 2 - GerversSofa.φ) (Real.pi / 2) ⊆
        Set.Ico (0 : ℝ) (Real.pi / 2) := fun x hx ↦ ⟨by linarith [hx.1], hx.2⟩
    have hsubB' : Set.Ico (Real.pi / 2 - GerversSofa.φ) (Real.pi / 2) ⊆
        Set.Ico (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2) :=
      fun x hx ↦ ⟨by linarith [hx.1], hx.2⟩
    simp only [gerverPhaseAngles, hJ4]
    refine Real.Angle.measure_restrict_image_congr_of_ae_eq measurableSet_Ico
      (fun T hT hTsub ↦ hdA.angleImage_eq_setLIntegral hturn hsubA hT (hTsub.trans hsub))
      (fun T hT hTsub ↦ hdB.angleImage_eq_setLIntegral hturn hsubB hT (hTsub.trans hsubB')) ?_
    filter_upwards [ae_restrict_Ico_mem_Ioo (μ := volume) (Real.pi / 2 - GerversSofa.φ)
      (Real.pi / 2)] with t ht
    rw [(hs4 t ht).1]
  · -- ### (5) the surface measure is the left tail on phase six
    have hsub : Set.Ioc (Real.pi / 2) (Real.pi / 2 + GerversSofa.φ) ⊆
        Set.Ioc (Real.pi / 2) Real.pi := fun x hx ↦ ⟨hx.1, by linarith [hx.2]⟩
    have hsubD' : Set.Ioc (Real.pi / 2) (Real.pi / 2 + GerversSofa.φ) ⊆
        Set.Ioc (Real.pi / 2) (Real.pi / 2 + GerversSofa.θ) :=
      fun x hx ↦ ⟨hx.1, by linarith [hx.2]⟩
    simp only [gerverPhaseAngles, hJ5]
    refine Real.Angle.measure_restrict_image_congr_of_ae_eq measurableSet_Ioc
      (fun T hT hTsub ↦ hdC.angleImage_eq_setLIntegral hturn hsubC hT (hTsub.trans hsub))
      (fun T hT hTsub ↦ hdD.angleImage_eq_setLIntegral hturn hsubD hT (hTsub.trans hsubD')) ?_
    filter_upwards [ae_restrict_Ioc_mem_Ioo (μ := volume) (Real.pi / 2)
      (Real.pi / 2 + GerversSofa.φ)] with u hu
    have h := (hs0 (u - Real.pi / 2) ⟨by linarith [hu.1], by linarith [hu.2]⟩).2
    rw [show u - Real.pi / 2 + Real.pi / 2 = u from by ring] at h
    rw [h]
  · -- ### (6) the surface measure is the left tail plus the corner measure on phase seven
    have hsub : Set.Ioc (Real.pi / 2 + GerversSofa.φ) (Real.pi / 2 + GerversSofa.θ) ⊆
        Set.Ioc (Real.pi / 2) Real.pi :=
      fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hsubD' : Set.Ioc (Real.pi / 2 + GerversSofa.φ) (Real.pi / 2 + GerversSofa.θ) ⊆
        Set.Ioc (Real.pi / 2) (Real.pi / 2 + GerversSofa.θ) :=
      fun x hx ↦ ⟨by linarith [hx.1], hx.2⟩
    have hsubI : Set.Ioc (Real.pi / 2 + GerversSofa.φ) (Real.pi / 2 + GerversSofa.θ) ⊆
        Set.Icc (0 : ℝ) Real.pi :=
      fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hsubO : Set.Ioc (Real.pi / 2 + GerversSofa.φ) (Real.pi / 2 + GerversSofa.θ) ⊆
        Set.Ioo (Real.pi / 2) Real.pi :=
      fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hcorner : ∀ T, MeasurableSet T →
        T ⊆ Set.Ioc (Real.pi / 2 + GerversSofa.φ) (Real.pi / 2 + GerversSofa.θ) →
        capCornerAngleMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' T) =
          ∫⁻ u in T,
            ENNReal.ofReal (-(paperGerverVelocityComponents (u - Real.pi / 2)).1) ∂volume := by
      intro T hT hTsub
      rw [capCornerAngleMeasure_angleImage_eq_setLIntegral K hT (hTsub.trans hsubI)]
      exact setLIntegral_congr_fun hT fun u hu ↦ by
        rw [capCornerDensity_eq_neg_velocity_normal K hK (hsubO (hTsub hu))]
    have hf0 : ∀ᵐ u ∂volume.restrict
        (Set.Ioc (Real.pi / 2 + GerversSofa.φ) (Real.pi / 2 + GerversSofa.θ)), 0 ≤ fD u :=
      ae_restrict_of_ae_restrict_of_subset hsubD' hdD.2.1
    have hg0 : ∀ᵐ u ∂volume.restrict
        (Set.Ioc (Real.pi / 2 + GerversSofa.φ) (Real.pi / 2 + GerversSofa.θ)),
        0 ≤ -(paperGerverVelocityComponents (u - Real.pi / 2)).1 := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      exact hα _ ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hsum : ∀ᵐ u ∂volume.restrict
        (Set.Ioc (Real.pi / 2 + GerversSofa.φ) (Real.pi / 2 + GerversSofa.θ)),
        fC u = fD u + -(paperGerverVelocityComponents (u - Real.pi / 2)).1 := by
      filter_upwards [ae_restrict_Ioc_mem_Ioo (μ := volume) (Real.pi / 2 + GerversSofa.φ)
        (Real.pi / 2 + GerversSofa.θ)] with u hu
      have h := (hs1 (u - Real.pi / 2) ⟨by linarith [hu.1], by linarith [hu.2]⟩).2
      rw [show u - Real.pi / 2 + Real.pi / 2 = u from by ring] at h
      rw [h]
      ring
    simp only [gerverPhaseAngles, hJ6]
    exact Real.Angle.measure_restrict_image_congr_add measurableSet_Ioc
      (fun T hT hTsub ↦ hdC.angleImage_eq_setLIntegral hturn hsubC hT (hTsub.trans hsub))
      (fun T hT hTsub ↦ hdD.angleImage_eq_setLIntegral hturn hsubD hT (hTsub.trans hsubD'))
      hcorner (hdD.1.aemeasurable.mono_measure (Measure.restrict_mono hsubD' le_rfl))
      hf0 hg0 hsum
  · -- ### (7) the surface measure is the corner measure on phases eight and nine
    have hsub : Set.Ioc (Real.pi / 2 + GerversSofa.θ) (Real.pi - GerversSofa.φ) ⊆
        Set.Ioc (Real.pi / 2) Real.pi :=
      fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hsubI : Set.Ioc (Real.pi / 2 + GerversSofa.θ) (Real.pi - GerversSofa.φ) ⊆
        Set.Icc (0 : ℝ) Real.pi :=
      fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hU : gerverPhaseAngles 7 ∪ gerverPhaseAngles 8 =
        (fun s : ℝ ↦ (s : Real.Angle)) ''
          Set.Ioc (Real.pi / 2 + GerversSofa.θ) (Real.pi - GerversSofa.φ) := by
      simp only [gerverPhaseAngles, hJ7, hJ8, ← Set.image_union,
        Set.Ioc_union_Ioc_eq_Ioc (by linarith : Real.pi / 2 + GerversSofa.θ ≤
          Real.pi - GerversSofa.θ) (by linarith : Real.pi - GerversSofa.θ ≤
          Real.pi - GerversSofa.φ)]
    rw [hU]
    refine Real.Angle.measure_restrict_image_congr_of_ae_eq measurableSet_Ioc
      (fun T hT hTsub ↦ hdC.angleImage_eq_setLIntegral hturn hsubC hT (hTsub.trans hsub))
      (fun T hT hTsub ↦ capCornerAngleMeasure_angleImage_eq_setLIntegral K hT
        (hTsub.trans hsubI)) ?_
    filter_upwards [ae_restrict_Ioc_mem_Ioo_union_Ioo (μ := volume)
      (Real.pi / 2 + GerversSofa.θ) (Real.pi - GerversSofa.θ)
      (Real.pi - GerversSofa.φ)] with u hu
    have hmem : u ∈ Set.Ioo (Real.pi / 2) Real.pi := by
      rcases hu with hu | hu
      · exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
      · exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
    rw [capCornerDensity_eq_neg_velocity_normal K hK hmem]
    rcases hu with hu | hu
    · have h := (hs2 (u - Real.pi / 2) ⟨by linarith [hu.1], by linarith [hu.2]⟩).2
      rw [show u - Real.pi / 2 + Real.pi / 2 = u from by ring] at h
      rw [h]
    · have h := (hs3 (u - Real.pi / 2) ⟨by linarith [hu.1], by linarith [hu.2]⟩).2
      rw [show u - Real.pi / 2 + Real.pi / 2 = u from by ring] at h
      rw [h]
  · -- ### (8) the surface measure vanishes on the last phase
    have hsub : Set.Ioc (Real.pi - GerversSofa.φ) Real.pi ⊆
        Set.Ioc (Real.pi / 2) Real.pi := fun x hx ↦ ⟨by linarith [hx.1], hx.2⟩
    simp only [gerverPhaseAngles, hJ9]
    rw [Measure.restrict_eq_zero,
      hdC.angleImage_eq_setLIntegral hturn hsubC measurableSet_Ioc hsub]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [ae_restrict_Ioc_mem_Ioo (μ := volume) (Real.pi - GerversSofa.φ)
      Real.pi] with u hu
    have h := (hs4 (u - Real.pi / 2) ⟨by linarith [hu.1], by linarith [hu.2]⟩).2
    rw [show u - Real.pi / 2 + Real.pi / 2 = u from by ring] at h
    rw [h, ENNReal.ofReal_zero]

end MovingSofa
