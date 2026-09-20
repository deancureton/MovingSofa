import MovingSofa.Area.ModuloLinear
import MovingSofa.Cap.InnerCornerVariation

/-!
# The outer corner and the two wedge segments, modulo convex-linear functionals

On the middle window `I = [φᴿ, φᴸ]` the outer corner of a cap is its inner corner translated by the
`K`-independent frame sum `c t = u_t + v_t`, so the two curve-area functionals differ by the two
mixed Stieltjes cross integrals, each convex-linear in `K`, plus the constant area of `c`.

The same happens at the two ends of the window: the tangent-line intersection point and the wedge
endpoint differ by a fixed vector, as do the outer and the inner corner, so each of the two
segment-area comparisons differs by a determinant that is affine in the support values and in the
inner corner, hence convex-linear in `K` as well.
-/

noncomputable section

open scoped unitInterval

namespace MovingSofa

/-! ### The outer corner path on the middle window -/

/-- The frame sum `t ↦ u_t + v_t`, as a continuous path of bounded variation. -/
def frameSumBV (a b : ℝ) : ContinuousBVPaths a b :=
  continuousBVOfContDiffOn
    (fun t ↦ normalVector (t : Real.Angle) + tangentVector (t : Real.Angle))
    ((contDiff_normalVector.add contDiff_tangentVector).of_le
      (by exact_mod_cast le_top)).contDiffOn

/-- The outer corner of a special cap on the middle window, as a continuous path of bounded
variation: the inner-corner path translated by the frame sum. -/
def capOuterMiddleBV (K : SpecialCapSpace) :
    ContinuousBVPaths paperGerverConstants.2.1 paperGerverConstants.2.2 :=
  capMiddleBV K + frameSumBV paperGerverConstants.2.1 paperGerverConstants.2.2

/-- The outer middle path of a special cap traces the outer corner of its body. -/
theorem capOuterMiddleBV_val (K : SpecialCapSpace)
    (s : Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2) :
    (capOuterMiddleBV K).val s =
      (rotatingHallwayParts (K.val.val : Set Point) ((s : ℝ) : Real.Angle)).outerCorner :=
  (outerCorner_eq_innerCorner_add K.val.val (s : ℝ)).symm

/-! ### The two end segments -/

/-- At the right Gerver angle the tangent-line intersection point is the right wedge endpoint
translated by a `K`-independent vector. -/
private theorem supportingIntersection_eq_wedgeEndpoints_add_fst (K : RightAngleCapSpace)
    (hcos : Real.cos paperGerverConstants.2.1 ≠ 0) :
    supportingIntersection K.val (paperGerverConstants.2.1 : Real.Angle)
        ((Real.pi / 2 : ℝ) : Real.Angle) =
      (wedgeEndpoints K paperGerverConstants.2.1).1 +
        !₂[(1 - Real.sin paperGerverConstants.2.1) /
          Real.cos paperGerverConstants.2.1, 1] := by
  have hangle : ((Real.pi / 2 : ℝ) : Real.Angle) - (paperGerverConstants.2.1 : Real.Angle) =
      ((Real.pi / 2 - paperGerverConstants.2.1 : ℝ) : Real.Angle) := by rw [Real.Angle.coe_sub]
  have hpyth := Real.sin_sq_add_cos_sq paperGerverConstants.2.1
  obtain ⟨hW0, hW1⟩ := wedgeEndpoints_fst_coords K paperGerverConstants.2.1
  rw [supportingIntersection, hangle, Real.Angle.cos_coe, Real.Angle.sin_coe,
    Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub, K.property.2.2.1]
  ext i
  fin_cases i <;>
    simp only [Fin.zero_eta, Fin.mk_one, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      normalVector, tangentVector, frame, Real.Angle.cos_coe, Real.Angle.sin_coe,
      Matrix.cons_val_zero, Matrix.cons_val_one, hW0, hW1]
  · field_simp
    linear_combination (supportValue (K.val : Set Point)
      (paperGerverConstants.2.1 : Real.Angle)) * hpyth
  · field_simp
    ring

/-- At the left Gerver angle the tangent-line intersection point is the left wedge endpoint
translated by a `K`-independent vector. -/
private theorem supportingIntersection_eq_wedgeEndpoints_add_snd (K : RightAngleCapSpace)
    (hsin : Real.sin paperGerverConstants.2.2 ≠ 0) :
    supportingIntersection K.val ((Real.pi / 2 : ℝ) : Real.Angle)
        ((Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle) =
      (wedgeEndpoints K paperGerverConstants.2.2).2 +
        !₂[(Real.cos paperGerverConstants.2.2 - 1) /
          Real.sin paperGerverConstants.2.2, 1] := by
  have hangle : ((Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle) -
      ((Real.pi / 2 : ℝ) : Real.Angle) = (paperGerverConstants.2.2 : Real.Angle) := by
    rw [← Real.Angle.coe_sub, show Real.pi / 2 + paperGerverConstants.2.2 - Real.pi / 2 =
      paperGerverConstants.2.2 from by ring]
  obtain ⟨hZ0, hZ1⟩ := wedgeEndpoints_snd_coords K paperGerverConstants.2.2
  rw [supportingIntersection, hangle, Real.Angle.cos_coe, Real.Angle.sin_coe,
    K.property.2.2.1]
  ext i
  fin_cases i <;>
    simp only [Fin.zero_eta, Fin.mk_one, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      normalVector, tangentVector, frame, Real.Angle.cos_coe, Real.Angle.sin_coe,
      Real.cos_pi_div_two, Real.sin_pi_div_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      hZ0, hZ1] <;>
    field_simp <;> ring_nf

/-- A pair of segment areas whose endpoints are fixed translates of a second pair differs from it
by a determinant, which is convex-linear as soon as the two base points are. -/
private theorem segmentArea_equivalent_of_translations {α : Type*} (cα : I → α → α → α)
    {W X P Q : α → Point} {v w : Point} (hP : ∀ K, P K = W K + w) (hQ : ∀ K, Q K = X K + v)
    (hW : ∀ (t : I) (K L : α), W (cα t K L) = (1 - (t : ℝ)) • W K + (t : ℝ) • W L)
    (hX : ∀ (t : I) (K L : α), X (cα t K L) = (1 - (t : ℝ)) • X K + (t : ℝ) • X L) :
    EquivalentModuloConvexLinear cα (fun K ↦ segmentArea (P K) (Q K))
      (fun K ↦ segmentArea (W K) (X K)) := by
  intro t K L
  simp only [hP, hQ, hW, hX, realCombination, segmentArea, planeCrossProduct, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul]
  ring

/-! ### The main equivalence -/

theorem cornerArea_equivalent_modulo_linear :
    ∃ F : SpecialCapSpace →
        ContinuousBVPaths paperGerverConstants.2.1 paperGerverConstants.2.2,
      (∀ K, (F K).val = fun t ↦
        (rotatingHallwayParts (K.val.val : Set Point) (t.val : Real.Angle)).outerCorner) ∧
      EquivalentModuloConvexLinear specialCapCombination
        (fun K ↦ curveAreaFunctional (F K))
        (fun K ↦ curveAreaFunctional (capMiddleBV K)) ∧
      EquivalentModuloConvexLinear specialCapCombination
        (fun K ↦ segmentArea
          (supportingIntersection K.val.val (paperGerverConstants.2.1 : Real.Angle)
            ((Real.pi / 2 : ℝ) : Real.Angle))
          (rotatingHallwayParts (K.val.val : Set Point)
            (paperGerverConstants.2.1 : Real.Angle)).outerCorner)
        (fun K ↦ segmentArea (distinguishedCapSides K.val).1.fanPoint
          (distinguishedCapSides K.val).1.corner) ∧
      EquivalentModuloConvexLinear specialCapCombination
        (fun K ↦ segmentArea
          (supportingIntersection K.val.val ((Real.pi / 2 : ℝ) : Real.Angle)
            ((Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle))
          (rotatingHallwayParts (K.val.val : Set Point)
            (paperGerverConstants.2.2 : Real.Angle)).outerCorner)
        (fun K ↦ segmentArea (distinguishedCapSides K.val).2.fanPoint
          (distinguishedCapSides K.val).2.corner) := by
  obtain ⟨hr, hl, -⟩ := paperGerverConstants_snd_mem_Ioo
  have hrl : paperGerverConstants.2.1 ≤ paperGerverConstants.2.2 :=
    paperGerverConstants_snd_fst_lt_snd_snd.le
  refine ⟨capOuterMiddleBV, fun K ↦ funext (capOuterMiddleBV_val K), ?_, ?_, ?_⟩
  -- ### The middle window: translation by the frame-sum path
  · intro t K L
    show curveAreaFunctional (capMiddleBV (specialCapCombination t K L) +
        frameSumBV paperGerverConstants.2.1 paperGerverConstants.2.2) -
      curveAreaFunctional (capMiddleBV (specialCapCombination t K L)) = _
    rw [capInnerCorner_variation.1 t K L]
    exact curveArea_translation_convexLinear hrl _ t (capMiddleBV K) (capMiddleBV L)
  -- ### The right end: both endpoints move by fixed vectors
  · have hcos : 0 < Real.cos paperGerverConstants.2.1 :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hr.1], hr.2⟩
    simp only [distinguishedCapSides_fst_fanPoint, distinguishedCapSides_fst_corner]
    refine segmentArea_equivalent_of_translations specialCapCombination
      (w := !₂[(1 - Real.sin paperGerverConstants.2.1) / Real.cos paperGerverConstants.2.1, 1])
      (v := normalVector (paperGerverConstants.2.1 : Real.Angle) +
        tangentVector (paperGerverConstants.2.1 : Real.Angle))
      (fun K ↦ supportingIntersection_eq_wedgeEndpoints_add_fst K.val hcos.ne')
      (fun K ↦ outerCorner_eq_innerCorner_add K.val.val paperGerverConstants.2.1)
      (fun t K L ↦ ?_) (fun t K L ↦ ?_)
    · show (wedgeEndpoints (specialCapCombination t K L).val paperGerverConstants.2.1).1 = _
      simp only [wedgeEndpoints, specialCap_isConvexDomain.1 t K L,
        supportValue_convexBodyCombination]
      match_scalars
      ring
    · exact capInnerCorner_of_eq_convexBodyCombination (specialCap_isConvexDomain.1 t K L)
        paperGerverConstants.2.1
  -- ### The left end: the same, with the complementary trigonometric normalisation
  · have hsin : 0 < Real.sin paperGerverConstants.2.2 :=
      Real.sin_pos_of_pos_of_lt_pi hl.1 (by linarith [Real.pi_pos, hl.2])
    simp only [distinguishedCapSides_snd_fanPoint, distinguishedCapSides_snd_corner]
    refine segmentArea_equivalent_of_translations specialCapCombination
      (w := !₂[(Real.cos paperGerverConstants.2.2 - 1) / Real.sin paperGerverConstants.2.2, 1])
      (v := normalVector (paperGerverConstants.2.2 : Real.Angle) +
        tangentVector (paperGerverConstants.2.2 : Real.Angle))
      (fun K ↦ supportingIntersection_eq_wedgeEndpoints_add_snd K.val hsin.ne')
      (fun K ↦ outerCorner_eq_innerCorner_add K.val.val paperGerverConstants.2.2)
      (fun t K L ↦ ?_) (fun t K L ↦ ?_)
    · show (wedgeEndpoints (specialCapCombination t K L).val paperGerverConstants.2.2).2 = _
      simp only [wedgeEndpoints, specialCap_isConvexDomain.1 t K L,
        supportValue_convexBodyCombination]
      match_scalars
      ring
    · exact capInnerCorner_of_eq_convexBodyCombination (specialCap_isConvexDomain.1 t K L)
        paperGerverConstants.2.2

end MovingSofa
