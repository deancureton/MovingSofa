import MovingSofa.Gerver.Niche.Orientation
import MovingSofa.Gerver.Injectivity

/-!
# The contact geometry of the paper Gerver sofa

Gerver's sofa is a monotone sofa, and its right-angle cap has all the contact geometry the
upper-bound argument reads off a monotone sofa: selected cap vertices and inner corner given
by the paper's curves `A`, `C` and `x`, a counterclockwise Jordan traversal of the niche
boundary, the interior of the base segment inside the niche and the three roof pieces outside
it, the two inner contact curves on the two inner walls of the supporting hallway, and the
signs of their stage speeds along the frame directions.

Every clause is about one and the same cap.  The cap is taken from `paperGerverCap_injectivity`
— which also supplies the density hypothesis that makes the selected contacts well defined —
and the caps produced by cap-support identification, niche identification and niche
orientation are identified with it through their common carrier `gerverOuterCap`.  The clauses
themselves are then assembled from the identification theorems together with
`gerver_bottom_segment_mem_gerverLiteralNiche`, the frame descriptions
`mem_rotatingHallwayParts_bRay_iff` and `mem_rotatingHallwayParts_dRay_iff` of the two inner
walls, the closed-interval velocity signs `paperGerverVelocityComponents_fst_nonpos` and
`paperGerverVelocityComponents_snd_nonneg`, and the stage speeds
`hasDerivWithinAt_paperGerverContacts_one_neg_smul` and
`hasDerivWithinAt_paperGerverContacts_three_pos_smul`.
-/

noncomputable section

namespace MovingSofa

theorem paperGerver_contact_geometry :
    IsMonotoneSofa paperGerverSofa ∧
    ∃ K : RightAngleCapSpace,
      (K.val : Set Point) = capOfSofa paperGerverSofa (Real.pi / 2) ∧
      ∃ hK : ∃ r s, HasCapDensities K r s,
        (∀ t : Set.Icc (0 : ℝ) (Real.pi / 2),
          (nondegenerateCapData K hK).1.1 t = paperGerverContacts t 0 ∧
          (nondegenerateCapData K hK).1.2 t = paperGerverContacts t 2 ∧
          capInnerCorner K t = paperGerverPath t) ∧
        (∃ Γ : ContinuousBVPaths 0 4, Γ.val = gerverNicheBoundary ∧
          IsOrientedJordanParametrization (by norm_num : (0 : ℝ) ≤ 4)
            (frontier (closure (capNiche K))) true Γ.val ∧
          closure (capNiche K) = jordanInterior (Set.range Γ.val) ∪ Set.range Γ.val ∧
          ClassicalResults.area (closure (capNiche K)) = ClassicalResults.area (capNiche K)) ∧
        (∀ a ∈ Set.Ioo (0 : ℝ) 1,
          (1 - a) • paperGerverContacts 0 3 +
            a • paperGerverContacts (Real.pi / 2) 1 ∈ capNiche K) ∧
        (∀ t ∈ Set.Icc (gerverStageTimes 3) (gerverStageTimes 5),
          paperGerverContacts t 1 ∉ capNiche K ∧
          paperGerverContacts t 1 ∈
            (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).bRay) ∧
        (∀ t ∈ Set.Icc (gerverStageTimes 1) (gerverStageTimes 4),
          paperGerverPath t ∉ capNiche K) ∧
        (∀ t ∈ Set.Icc (gerverStageTimes 0) (gerverStageTimes 2),
          paperGerverContacts t 3 ∉ capNiche K ∧
          paperGerverContacts t 3 ∈
            (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).dRay) ∧
        (∀ i : Fin 5, i = 3 ∨ i = 4 → ∀ t ∈ gerverStageIntervals i,
          ∃ c : ℝ, c < 0 ∧
            HasDerivWithinAt (fun s ↦ paperGerverContacts s 1)
              (c • tangentVector (t : Real.Angle)) (gerverStageIntervals i) t) ∧
        (∀ i : Fin 5, i = 0 ∨ i = 1 → ∀ t ∈ gerverStageIntervals i,
          ∃ c : ℝ, 0 < c ∧
            HasDerivWithinAt (fun s ↦ paperGerverContacts s 3)
              (c • normalVector (t : Real.Angle)) (gerverStageIntervals i) t) := by
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  have hangsum : ∀ t : ℝ, (t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle) =
      ((Real.pi / 2 + t : ℝ) : Real.Angle) := fun t => by
    rw [← Real.Angle.coe_add, add_comm]
  have ht0 : gerverStageTimes 0 = 0 := gerverStageTimes_zero
  have ht5 : gerverStageTimes 5 = Real.pi / 2 := rfl
  have h03 : (0 : ℝ) < gerverStageTimes 3 := by
    rw [← ht0]; exact gerverStageTimes_strictMono (by decide)
  have h25 : gerverStageTimes 2 < Real.pi / 2 := by
    rw [← ht5]; exact gerverStageTimes_strictMono (by decide)
  -- ### One cap serves every clause: the four theorems below all speak about `gerverOuterCap`
  obtain ⟨K, hKset, ⟨r, s, hdens, -⟩, -, -⟩ := paperGerverCap_injectivity
  have hK : ∃ r s, HasCapDensities K r s := ⟨r, s, hdens⟩
  obtain ⟨-, hGeq, -, -, hcapeq, ⟨K₁, hK₁set, hsing, hA0, hAT, hC0, hCT⟩, hsup⟩ :=
    gerver_capSupport_identification
  have hKcarrier : (K.val : Set Point) = gerverOuterCap := by rw [hKset, hGeq, hcapeq]
  have hcapK : ∀ K' : RightAngleCapSpace, (K'.val : Set Point) = gerverOuterCap → K' = K :=
    fun K' h => Subtype.ext (SetLike.coe_injective (h.trans hKcarrier.symm))
  rw [hcapK K₁ hK₁set] at hsing hA0 hAT hC0 hCT
  obtain ⟨-, ⟨K₂, hK₂set, hniche⟩, -, hmono⟩ := gerver_paperNiche_identification
  rw [hcapK K₂ hK₂set] at hniche
  obtain ⟨K₃, hK₃set, Γ, hΓ, hOJP, hclos, harea, -, hnotB, hnotx, hnotD⟩ :=
    gerver_niche_orientation
  rw [hcapK K₃ hK₃set] at hOJP hclos harea hnotB hnotx hnotD
  -- ### The two support values of the cap, and the resulting inner corner
  have hsupK : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      supportValue (K.val : Set Point) (t : Real.Angle) =
        inner ℝ (paperGerverPath t) (normalVector (t : Real.Angle)) + 1 ∧
      supportValue (K.val : Set Point) ((Real.pi / 2 + t : ℝ) : Real.Angle) =
        inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) + 1 := by
    rw [hKcarrier]
    exact hsup gerverOuterCap (Or.inl rfl)
  have hcorner : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      capInnerCorner K t = paperGerverPath t := by
    intro t ht
    rw [capInnerCorner,
      (rotatingHallwayParts_formulas (K.val : Set Point) (t : Real.Angle)).2.1, hangsum,
      (hsupK t ht).1, (hsupK t ht).2, add_sub_cancel_right, add_sub_cancel_right,
      inner_normalVector_smul_add_inner_tangentVector_smul]
  refine ⟨hmono, K, hKset, hK, ?_, ⟨Γ, hΓ, hOJP, hclos, harea⟩, ?_, ?_, hnotx, ?_,
    fun i hi t ht => hasDerivWithinAt_paperGerverContacts_one_neg_smul hi ht,
    fun i hi t ht => hasDerivWithinAt_paperGerverContacts_three_pos_smul hi ht⟩
  · -- ### The selected cap vertices and the inner corner
    -- Strictly inside the interval the two exposed faces are singletons; at the two endpoints
    -- the selected contacts are the frozen one-sided contacts of cap-support identification,
    -- with the nondegeneracy proposition equating the two vertices at `π / 2`.
    intro t
    have htI : (t : ℝ) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := t.2
    refine ⟨?_, ?_, hcorner t htI⟩
    · dsimp only [nondegenerateCapData]
      split_ifs with hT
      · rw [hT, hAT]
        rfl
      · rcases eq_or_lt_of_le htI.1 with h0 | h0
        · rw [← h0, hA0]
          exact congrArg (fun a : Real.Angle ↦ (edgeVertices (K.val) a).1) Real.Angle.coe_zero
        · have hmem : (t : ℝ) ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
            ⟨h0, lt_of_le_of_ne htI.2 hT⟩
          show (edgeVertices (K.val) ((t : ℝ) : Real.Angle)).1 = _
          rw [edgeVertices_eq_of_exposedEdge_singleton (hsing _ hmem).1]
    · show (edgeVertices (K.val) (((t : ℝ) + Real.pi / 2 : ℝ) : Real.Angle)).1 = _
      rcases eq_or_lt_of_le htI.1 with h0 | h0
      · rw [← h0, zero_add, hC0]
      rcases eq_or_lt_of_le htI.2 with hT | hT
      · have hnd : (edgeVertices (K.val) ((Real.pi / 2 + Real.pi / 2 : ℝ) : Real.Angle)).1 =
            (edgeVertices (K.val) ((Real.pi / 2 + Real.pi / 2 : ℝ) : Real.Angle)).2 :=
          ((capDensities_contact_eq K hK).2 (Real.pi / 2) ⟨hpi, le_rfl⟩).1
        rw [hT, hnd, hCT]
        exact congrArg (fun a : Real.Angle ↦ (edgeVertices (K.val) a).2)
          (congrArg (fun x : ℝ ↦ (x : Real.Angle)) (by ring))
      · rw [edgeVertices_eq_of_exposedEdge_singleton (hsing _ ⟨h0, hT⟩).2]
  · -- ### The open base segment lies in the niche
    intro a ha
    rw [hniche]
    exact gerver_bottom_segment_mem_gerverLiteralNiche ha
  · -- ### The second contact curve lies on the downward inner wall
    -- With `B = x + α v`, the two support values turn the wall condition into `α t ≤ 0`.
    intro t ht
    refine ⟨hnotB t ht, ?_⟩
    have htI : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [ht.1], by rw [← ht5]; exact ht.2⟩
    rw [mem_rotatingHallwayParts_bRay_iff, hangsum, (hsupK t htI).1, (hsupK t htI).2,
      add_sub_cancel_right, add_sub_cancel_right]
    have hB : paperGerverContacts t 1 =
        paperGerverPath t + (paperGerverVelocityComponents t).1 •
          tangentVector (t : Real.Angle) := rfl
    rw [hB, inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      inner_tangentVector_normalVector_real t t, sub_self, Real.sin_zero,
      inner_tangentVector_self]
    exact ⟨by ring, by nlinarith [paperGerverVelocityComponents_fst_nonpos htI]⟩
  · -- ### The fourth contact curve lies on the leftward inner wall
    -- With `D = x - β u`, the same two support values turn the wall condition into `0 ≤ β t`.
    intro t ht
    refine ⟨hnotD t ht, ?_⟩
    have htI : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
      ⟨by rw [← ht0]; exact ht.1, by linarith [ht.2]⟩
    rw [mem_rotatingHallwayParts_dRay_iff, hangsum, (hsupK t htI).1, (hsupK t htI).2,
      add_sub_cancel_right, add_sub_cancel_right]
    have hD : paperGerverContacts t 3 =
        paperGerverPath t - (paperGerverVelocityComponents t).2 •
          normalVector (t : Real.Angle) := rfl
    rw [hD, inner_sub_left, inner_sub_left, real_inner_smul_left, real_inner_smul_left,
      inner_normalVector_self, inner_normalVector_tangentVector]
    exact ⟨by nlinarith [paperGerverVelocityComponents_snd_nonneg htI], by ring⟩

end MovingSofa
