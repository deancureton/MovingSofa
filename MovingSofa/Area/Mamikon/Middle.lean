import MovingSofa.Area.Mamikon.Tails
import MovingSofa.Cap.CornerModuloLinear
import MovingSofa.Cap.UpperBoundaryTracing

/-!
# The middle Mamikon functional of a special cap

`middleMamikon` is the evaluated four-term Mamikon decomposition of the part of a special cap's
niche cut out by the two straight tangent paths on `[0, φᴿ]` and `[φᴸ, π / 2]`, the outer-corner arc
on the middle window `[φᴿ, φᴸ]` and the terminal tangent path on `[π / 2, π]`.  This module proves
that it agrees with `-upperBoundMiddle` modulo convex-linear functionals of the cap.

The four summands already express their straight paths as endpoint segment areas, so the whole
functional is a sum of eleven signed segment areas, one curve area and four convex arc areas.  The
four arc areas add up to the cap area modulo a convex-linear functional
(`specialCapArea_equivalent_upper_arcs`), which supplies the `-|K|` of the upper bound.  Of the
eleven segments, five are convex-linear and therefore discarded
(`middleMamikon_segments_isConvexLinear`): all their endpoints move convex-linearly with the cap and
stay on the two fixed horizontal lines `y = 0` and `y = 1`, the latter being the top supporting
line, so no determinant of two moving coordinates ever appears.  Two more pairs collapse at the two
Gerver angles, where the extreme faces are singletons: at `φᴿ` the tangent-line intersection, the
face and the outer corner are collinear, so the two segments merge
(`middleMamikon_segments_merge_right`), and at `φᴸ` the tangent-line intersection *is* the outer
corner, so the two segments cancel (`middleMamikon_segments_cancel_left`).  What remains are exactly
the three comparisons of `cornerArea_equivalent_modulo_linear`, the last of them reversed.
-/

noncomputable section

namespace MovingSofa

def straightMamikonValue (K : ConvexBody Point) (a b : ℝ) (p q : Point) : ℝ :=
  segmentArea (edgeVertices K (a : Real.Angle)).1 p + segmentArea p q +
    segmentArea q (edgeVertices K (b : Real.Angle)).2 - convexArcArea K a b

def middleMamikon (K : SpecialCapSpace) : ℝ :=
  let B := K.val.val
  let r := paperGerverConstants.2.1
  let l := paperGerverConstants.2.2
  let T := Real.pi / 2
  let y := fun t : ℝ ↦ (rotatingHallwayParts (B : Set Point) (t : Real.Angle)).outerCorner
  straightMamikonValue B 0 r
      (supportingIntersection B 0 (T : Real.Angle))
      (supportingIntersection B (r : Real.Angle) (T : Real.Angle)) +
    (segmentArea (edgeVertices B (r : Real.Angle)).1 (y r) +
      curveAreaFunctional (capOuterMiddleBV K) +
      segmentArea (y l) (edgeVertices B (l : Real.Angle)).2 - convexArcArea B r l) +
    straightMamikonValue B l T
      (supportingIntersection B (l : Real.Angle) ((T + l : ℝ) : Real.Angle))
      (supportingIntersection B (T : Real.Angle) ((T + l : ℝ) : Real.Angle)) +
    tangentMamikonValue B T Real.pi

/-! ### The singleton faces of a special cap and their positions -/

/-- The extreme faces of a special cap at the upper normals other than the vertical one are
singletons, because its injectivity condition supplies angular densities. -/
private theorem specialCap_edgeVertices_eq (K : SpecialCapSpace) {t : ℝ}
    (ht : t ∈ Set.Icc 0 Real.pi) (htop : t ≠ Real.pi / 2) :
    (edgeVertices K.val.val (t : Real.Angle)).1 =
      (edgeVertices K.val.val (t : Real.Angle)).2 := by
  obtain ⟨r, s, hdens, -⟩ := K.property.1.1
  exact capDensities_edgeVertices_eq K.val ⟨r, s, hdens⟩ ht htop

/-- Both horizontal extreme faces of a special cap lie on the base line: they are singletons, and a
singleton horizontal face of a right-angle cap cannot have positive height. -/
private theorem specialCap_horizontal_edgeVertices_apply_one (K : SpecialCapSpace) :
    (edgeVertices K.val.val ((0 : ℝ) : Real.Angle)).1 1 = 0 ∧
      (edgeVertices K.val.val ((Real.pi : ℝ) : Real.Angle)).2 1 = 0 := by
  have hpi := Real.pi_pos
  have h0 := specialCap_edgeVertices_eq K (t := 0) ⟨le_rfl, hpi.le⟩
    (by positivity : (0 : ℝ) < Real.pi / 2).ne
  have hp := specialCap_edgeVertices_eq K (t := Real.pi) ⟨hpi.le, le_rfl⟩
    (by linarith : Real.pi / 2 < Real.pi).ne'
  refine ⟨K.val.edgeVertices_fst_apply_one_eq_zero Real.sin_zero h0, ?_⟩
  rw [← hp]
  exact K.val.edgeVertices_fst_apply_one_eq_zero Real.sin_pi hp

/-- At the left Gerver angle the two supporting lines of the middle Mamikon loop are at angular
difference `π / 2`, so they meet at the outer corner of the supporting hallway. -/
private theorem specialCap_supportingIntersection_left_eq_outerCorner (K : SpecialCapSpace) :
    supportingIntersection K.val.val (paperGerverConstants.2.2 : Real.Angle)
        ((Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle) =
      (rotatingHallwayParts (K.val.val : Set Point)
        (paperGerverConstants.2.2 : Real.Angle)).outerCorner := by
  rw [show (Real.pi / 2 + paperGerverConstants.2.2 : ℝ) =
    paperGerverConstants.2.2 + Real.pi / 2 from by ring]
  exact supportingIntersection_add_pi_div_two_eq_outerCorner _ _

/-! ### The convex-linear segments -/

/-- The signed area of the segment between two convex-linear point functionals of a special cap
that both keep a constant height is convex-linear. -/
private theorem segmentArea_isConvexLinear_of_apply_one_eq (P Q : SpecialCapSpace → Point)
    {a b : ℝ}
    (hP : ∀ (t : unitInterval) (K L : SpecialCapSpace),
      P (specialCapCombination t K L) = (1 - (t : ℝ)) • P K + (t : ℝ) • P L)
    (hQ : ∀ (t : unitInterval) (K L : SpecialCapSpace),
      Q (specialCapCombination t K L) = (1 - (t : ℝ)) • Q K + (t : ℝ) • Q L)
    (hPa : ∀ K, P K 1 = a) (hQb : ∀ K, Q K 1 = b) :
    IsConvexLinear specialCapCombination realCombination fun K ↦ segmentArea (P K) (Q K) :=
  fun t K L ↦ by
    show segmentArea (P (specialCapCombination t K L)) (Q (specialCapCombination t K L)) =
      realCombination t (segmentArea (P K) (Q K)) (segmentArea (P L) (Q L))
    rw [hP, hQ, realCombination]
    exact segmentArea_combination_of_apply_one_eq _ ((hPa K).trans (hPa L).symm)
      ((hQb K).trans (hQb L).symm)

/-- The five straight segments that the reductions leave in place have convex-linear total signed
area.  In the order of the four-term definition they are the bottom segment at the horizontal normal
`0`, the chord of the top supporting line from `l_K^T(0)` to `l_K^T(φᴿ)`, the chord from
`l_K^{T + φᴸ}(T)` to the negative top vertex `v_K^-(T)`, the chord from the positive top vertex
`v_K^+(T)` to `l_K^π(T)`, and the bottom segment at the normal `π`.  All ten endpoints are
convex-linear in the cap, and each lies on one of the two fixed horizontal lines `y = 0` — the two
singleton horizontal contacts — and `y = 1` — the top supporting line. -/
private theorem middleMamikon_segments_isConvexLinear :
    IsConvexLinear specialCapCombination realCombination fun K ↦
      segmentArea (edgeVertices K.val.val ((0 : ℝ) : Real.Angle)).1
          (supportingIntersection K.val.val 0 ((Real.pi / 2 : ℝ) : Real.Angle)) +
        segmentArea (supportingIntersection K.val.val 0 ((Real.pi / 2 : ℝ) : Real.Angle))
          (supportingIntersection K.val.val (paperGerverConstants.2.1 : Real.Angle)
            ((Real.pi / 2 : ℝ) : Real.Angle)) +
        segmentArea (supportingIntersection K.val.val ((Real.pi / 2 : ℝ) : Real.Angle)
            ((Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle))
          (edgeVertices K.val.val ((Real.pi / 2 : ℝ) : Real.Angle)).2 +
        segmentArea (edgeVertices K.val.val ((Real.pi / 2 : ℝ) : Real.Angle)).1
          (supportingIntersection K.val.val ((Real.pi / 2 : ℝ) : Real.Angle)
            ((Real.pi : ℝ) : Real.Angle)) +
        segmentArea (supportingIntersection K.val.val ((Real.pi / 2 : ℝ) : Real.Angle)
            ((Real.pi : ℝ) : Real.Angle))
          (edgeVertices K.val.val ((Real.pi : ℝ) : Real.Angle)).2 := by
  have hpi := Real.pi_pos
  obtain ⟨hr, hl, -⟩ := paperGerverConstants_snd_mem_Ioo
  -- ### The endpoints move convex-linearly
  have hev := fun (a : Real.Angle) (t : unitInterval) (M N : SpecialCapSpace) ↦
    (specialCap_maps_linear t M N).1 a
  have hsi := fun (a b : ℝ) (hab : a < b) (hba : b < a + Real.pi) (t : unitInterval)
    (M N : SpecialCapSpace) ↦ (specialCap_maps_linear t M N).2 a b hab hba
  have hsi0 : ∀ (t : unitInterval) (M N : SpecialCapSpace),
      supportingIntersection (specialCapCombination t M N).val.val 0
          ((Real.pi / 2 : ℝ) : Real.Angle) =
        (1 - (t : ℝ)) • supportingIntersection M.val.val 0 ((Real.pi / 2 : ℝ) : Real.Angle) +
          (t : ℝ) • supportingIntersection N.val.val 0 ((Real.pi / 2 : ℝ) : Real.Angle) :=
    fun t M N ↦ by
      simpa only [Real.Angle.coe_zero] using
        hsi 0 (Real.pi / 2) (by positivity) (by linarith) t M N
  -- ### The endpoints keep their heights
  have htop : ∀ (M : SpecialCapSpace) (p : Point),
      inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) =
        supportValue (M.val.val : Set Point) ((Real.pi / 2 : ℝ) : Real.Angle) → p 1 = 1 :=
    fun M _ hp ↦ M.val.apply_one_eq_one hp
  have hsiL : ∀ (M : SpecialCapSpace) (s : ℝ),
      supportingIntersection M.val.val ((Real.pi / 2 : ℝ) : Real.Angle) (s : Real.Angle) 1 = 1 :=
    fun M s ↦ htop M _ (supportingIntersection_inner_left _ _ s)
  have hsiR : ∀ (M : SpecialCapSpace) (s : ℝ), Real.sin (Real.pi / 2 - s) ≠ 0 →
      supportingIntersection M.val.val (s : Real.Angle) ((Real.pi / 2 : ℝ) : Real.Angle) 1 = 1 :=
    fun M s hs ↦ htop M _ (supportingIntersection_inner_right _ s _ hs)
  have hsi0h : ∀ M : SpecialCapSpace,
      supportingIntersection M.val.val 0 ((Real.pi / 2 : ℝ) : Real.Angle) 1 = 1 := fun M ↦ by
    simpa only [Real.Angle.coe_zero] using
      hsiR M 0 (by rw [sub_zero, Real.sin_pi_div_two]; norm_num)
  have hvtop : ∀ M : SpecialCapSpace,
      (edgeVertices M.val.val ((Real.pi / 2 : ℝ) : Real.Angle)).1 1 = 1 ∧
        (edgeVertices M.val.val ((Real.pi / 2 : ℝ) : Real.Angle)).2 1 = 1 :=
    fun M ↦ ⟨htop M _ (edgeVertices_fst_mem _ _).2, htop M _ (edgeVertices_snd_mem _ _).2⟩
  have hsinr : Real.sin (Real.pi / 2 - paperGerverConstants.2.1) ≠ 0 := by
    rw [Real.sin_pi_div_two_sub]
    exact (Real.cos_pos_of_mem_Ioo ⟨by linarith [hr.1], hr.2⟩).ne'
  -- ### The five segments
  have h1 := segmentArea_isConvexLinear_of_apply_one_eq
    (fun M ↦ (edgeVertices M.val.val ((0 : ℝ) : Real.Angle)).1)
    (fun M ↦ supportingIntersection M.val.val 0 ((Real.pi / 2 : ℝ) : Real.Angle))
    (fun t M N ↦ (hev _ t M N).1) hsi0
    (fun M ↦ (specialCap_horizontal_edgeVertices_apply_one M).1) hsi0h
  have h2 := segmentArea_isConvexLinear_of_apply_one_eq
    (fun M ↦ supportingIntersection M.val.val 0 ((Real.pi / 2 : ℝ) : Real.Angle))
    (fun M ↦ supportingIntersection M.val.val (paperGerverConstants.2.1 : Real.Angle)
      ((Real.pi / 2 : ℝ) : Real.Angle))
    hsi0 (hsi paperGerverConstants.2.1 (Real.pi / 2) hr.2 (by linarith [hr.1]))
    hsi0h (fun M ↦ hsiR M paperGerverConstants.2.1 hsinr)
  have h3 := segmentArea_isConvexLinear_of_apply_one_eq
    (fun M ↦ supportingIntersection M.val.val ((Real.pi / 2 : ℝ) : Real.Angle)
      ((Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle))
    (fun M ↦ (edgeVertices M.val.val ((Real.pi / 2 : ℝ) : Real.Angle)).2)
    (hsi (Real.pi / 2) (Real.pi / 2 + paperGerverConstants.2.2) (by linarith [hl.1])
      (by linarith [hl.2]))
    (fun t M N ↦ (hev _ t M N).2)
    (fun M ↦ hsiL M (Real.pi / 2 + paperGerverConstants.2.2)) (fun M ↦ (hvtop M).2)
  have h4 := segmentArea_isConvexLinear_of_apply_one_eq
    (fun M ↦ (edgeVertices M.val.val ((Real.pi / 2 : ℝ) : Real.Angle)).1)
    (fun M ↦ supportingIntersection M.val.val ((Real.pi / 2 : ℝ) : Real.Angle)
      ((Real.pi : ℝ) : Real.Angle))
    (fun t M N ↦ (hev _ t M N).1) (hsi (Real.pi / 2) Real.pi (by linarith) (by linarith))
    (fun M ↦ (hvtop M).1) (fun M ↦ hsiL M Real.pi)
  have h5 := segmentArea_isConvexLinear_of_apply_one_eq
    (fun M ↦ supportingIntersection M.val.val ((Real.pi / 2 : ℝ) : Real.Angle)
      ((Real.pi : ℝ) : Real.Angle))
    (fun M ↦ (edgeVertices M.val.val ((Real.pi : ℝ) : Real.Angle)).2)
    (hsi (Real.pi / 2) Real.pi (by linarith) (by linarith)) (fun t M N ↦ (hev _ t M N).2)
    (fun M ↦ hsiL M Real.pi)
    (fun M ↦ (specialCap_horizontal_edgeVertices_apply_one M).2)
  intro t M N
  have e1 := h1 t M N
  have e2 := h2 t M N
  have e3 := h3 t M N
  have e4 := h4 t M N
  have e5 := h5 t M N
  simp only [realCombination] at e1 e2 e3 e4 e5 ⊢
  linear_combination e1 + e2 + e3 + e4 + e5

/-! ### The two collapsing pairs at the Gerver angles -/

/-- At the right Gerver angle the tangent-line intersection, the singleton extreme face and the
outer corner all lie on the same supporting line, so the two segments through the face merge into a
single chord. -/
private theorem middleMamikon_segments_merge_right (K : SpecialCapSpace) :
    segmentArea (supportingIntersection K.val.val (paperGerverConstants.2.1 : Real.Angle)
          ((Real.pi / 2 : ℝ) : Real.Angle))
        (edgeVertices K.val.val (paperGerverConstants.2.1 : Real.Angle)).2 +
      segmentArea (edgeVertices K.val.val (paperGerverConstants.2.1 : Real.Angle)).1
        (rotatingHallwayParts (K.val.val : Set Point)
          (paperGerverConstants.2.1 : Real.Angle)).outerCorner =
    segmentArea (supportingIntersection K.val.val (paperGerverConstants.2.1 : Real.Angle)
        ((Real.pi / 2 : ℝ) : Real.Angle))
      (rotatingHallwayParts (K.val.val : Set Point)
        (paperGerverConstants.2.1 : Real.Angle)).outerCorner := by
  have hpi := Real.pi_pos
  obtain ⟨hr, -, -⟩ := paperGerverConstants_snd_mem_Ioo
  have h1 := supportingIntersection_inner_left K.val.val paperGerverConstants.2.1 (Real.pi / 2)
  have h2 : inner ℝ (edgeVertices K.val.val (paperGerverConstants.2.1 : Real.Angle)).2
      (normalVector (paperGerverConstants.2.1 : Real.Angle)) =
      supportValue (K.val.val : Set Point) (paperGerverConstants.2.1 : Real.Angle) :=
    (edgeVertices_snd_mem _ _).2
  have h3 : inner ℝ (rotatingHallwayParts (K.val.val : Set Point)
      (paperGerverConstants.2.1 : Real.Angle)).outerCorner
      (normalVector (paperGerverConstants.2.1 : Real.Angle)) =
      supportValue (K.val.val : Set Point) (paperGerverConstants.2.1 : Real.Angle) := by
    rw [outerCorner_eq_support_sum, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      inner_normalVector_self, inner_tangentVector_normalVector_real, sub_self, Real.sin_zero]
    ring
  have h := segmentArea_sub_segmentArea_of_inner_normalVector_eq h1 h3 h2
  rw [specialCap_edgeVertices_eq K ⟨hr.1.le, by linarith [hr.2]⟩ hr.2.ne]
  linarith [segmentArea_swap (edgeVertices K.val.val
    (paperGerverConstants.2.1 : Real.Angle)).2
    (rotatingHallwayParts (K.val.val : Set Point)
      (paperGerverConstants.2.1 : Real.Angle)).outerCorner]

/-- At the left Gerver angle the extreme face is a single point and the tangent-line intersection is
the outer corner, so the two segments through the face cancel by antisymmetry. -/
private theorem middleMamikon_segments_cancel_left (K : SpecialCapSpace) :
    segmentArea (rotatingHallwayParts (K.val.val : Set Point)
          (paperGerverConstants.2.2 : Real.Angle)).outerCorner
        (edgeVertices K.val.val (paperGerverConstants.2.2 : Real.Angle)).2 +
      segmentArea (edgeVertices K.val.val (paperGerverConstants.2.2 : Real.Angle)).1
        (supportingIntersection K.val.val (paperGerverConstants.2.2 : Real.Angle)
          ((Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle)) = 0 := by
  have hpi := Real.pi_pos
  obtain ⟨-, hl, -⟩ := paperGerverConstants_snd_mem_Ioo
  rw [specialCap_supportingIntersection_left_eq_outerCorner,
    specialCap_edgeVertices_eq K ⟨hl.1.le, by linarith [hl.2]⟩ hl.2.ne]
  linarith [segmentArea_swap (rotatingHallwayParts (K.val.val : Set Point)
    (paperGerverConstants.2.2 : Real.Angle)).outerCorner
    (edgeVertices K.val.val (paperGerverConstants.2.2 : Real.Angle)).2]

/-! ### The equivalence -/

theorem middleMamikon_equivalent_neg_upperBoundMiddle :
    EquivalentModuloConvexLinear specialCapCombination middleMamikon
      (fun K ↦ -upperBoundMiddle K) := by
  obtain ⟨F, hFval, hmid, hright, hleft⟩ := cornerArea_equivalent_modulo_linear
  have hF : ∀ M : SpecialCapSpace, F M = capOuterMiddleBV M := fun M ↦
    Subtype.ext ((hFval M).trans (funext (capOuterMiddleBV_val M)).symm)
  -- The chord closing the third straight path reverses the left comparison chord.
  have hrev : ∀ M : SpecialCapSpace,
      segmentArea (supportingIntersection M.val.val (paperGerverConstants.2.2 : Real.Angle)
            ((Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle))
          (supportingIntersection M.val.val ((Real.pi / 2 : ℝ) : Real.Angle)
            ((Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle)) =
        -segmentArea (supportingIntersection M.val.val ((Real.pi / 2 : ℝ) : Real.Angle)
            ((Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle))
          (rotatingHallwayParts (M.val.val : Set Point)
            (paperGerverConstants.2.2 : Real.Angle)).outerCorner := fun M ↦ by
    rw [specialCap_supportingIntersection_left_eq_outerCorner]
    exact segmentArea_swap _ _
  -- The right wedge segment of the upper bound runs in the opposite orientation.
  have hswap : ∀ M : SpecialCapSpace,
      segmentArea (distinguishedCapSides M.val).1.corner
          (distinguishedCapSides M.val).1.fanPoint =
        -segmentArea (distinguishedCapSides M.val).1.fanPoint
          (distinguishedCapSides M.val).1.corner := fun M ↦ segmentArea_swap _ _
  intro t K L
  have e1 := specialCapArea_equivalent_upper_arcs t K L
  have e2 := hmid t K L
  have e3 := hright t K L
  have e4 := hleft t K L
  have f := middleMamikon_segments_isConvexLinear t K L
  simp only [hF, realCombination] at e1 e2 e3 e4 f
  simp only [middleMamikon, straightMamikonValue, tangentMamikonValue, upperBoundMiddle,
    realCombination, hrev, hswap]
  linear_combination f + e1 + e2 + e3 - e4 +
    middleMamikon_segments_merge_right (specialCapCombination t K L) +
    middleMamikon_segments_cancel_left (specialCapCombination t K L) -
    (1 - (t : ℝ)) * (middleMamikon_segments_merge_right K +
      middleMamikon_segments_cancel_left K) -
    (t : ℝ) * (middleMamikon_segments_merge_right L +
      middleMamikon_segments_cancel_left L)

end MovingSofa
