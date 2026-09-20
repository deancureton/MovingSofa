import MovingSofa.Cap.Contacts
import MovingSofa.Analysis.SurfaceMeasure.Properties

noncomputable section

open MeasureTheory

namespace MovingSofa

theorem capTangentArm_identities (K : RightAngleCapSpace) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).outerCorner =
      (capVertices K t).1.1 + (tangentArmLengths K t).1.1 • tangentVector (t : Real.Angle) ∧
    (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).outerCorner =
      (capVertices K t).1.2 + (tangentArmLengths K t).1.2 • tangentVector (t : Real.Angle) ∧
    (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).outerCorner =
      (capVertices K t).2.1 + (tangentArmLengths K t).2.1 • normalVector (t : Real.Angle) ∧
    (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).outerCorner =
      (capVertices K t).2.2 + (tangentArmLengths K t).2.2 • normalVector (t : Real.Angle) := by
  have hrot : rotationMap (t : Real.Angle) (!₂[1, 1] : Point) =
      normalVector (t : Real.Angle) + tangentVector (t : Real.Angle) := by
    unfold rotationMap
    rw [Orientation.rotation_apply, rightAngleRotation_apply]
    ext i
    fin_cases i <;> simp [normalVector, tangentVector, frame]
    ring
  have hy : (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).outerCorner =
      supportValue K.val (t : Real.Angle) • normalVector (t : Real.Angle) +
      supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) • tangentVector (t : Real.Angle) := by
    simp only [rotatingHallwayParts, supportingPlacement, hallwayParts, hrot, Real.Angle.coe_add]
    module
  have hnn : inner ℝ (normalVector (t : Real.Angle)) (normalVector (t : Real.Angle)) = 1 := by
    rw [PiLp.inner_apply]
    simp [normalVector, frame, Fin.sum_univ_two, Real.cos_sq_add_sin_sq]
  have htt : inner ℝ (tangentVector (t : Real.Angle)) (tangentVector (t : Real.Angle)) = 1 := by
    rw [PiLp.inner_apply]
    simp [tangentVector, frame, Fin.sum_univ_two, Real.sin_sq_add_cos_sq]
  have hnt : inner ℝ (normalVector (t : Real.Angle)) (tangentVector (t : Real.Angle)) = 0 := by
    simp [normalVector, tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
    ring
  have htn : inner ℝ (tangentVector (t : Real.Angle)) (normalVector (t : Real.Angle)) = 0 := by
    rw [real_inner_comm, hnt]
  have hA (a b c : ℝ) :
      a • normalVector (t : Real.Angle) + b • tangentVector (t : Real.Angle) =
      (a • normalVector (t : Real.Angle) + c • tangentVector (t : Real.Angle)) +
        inner ℝ ((a • normalVector (t : Real.Angle) + b • tangentVector (t : Real.Angle)) -
          (a • normalVector (t : Real.Angle) + c • tangentVector (t : Real.Angle)))
          (tangentVector (t : Real.Angle)) • tangentVector (t : Real.Angle) := by
    simp only [inner_sub_left, inner_add_left, real_inner_smul_left, hnt, htt]
    module
  have hC (a b c : ℝ) :
      a • normalVector (t : Real.Angle) + b • tangentVector (t : Real.Angle) =
      (b • tangentVector (t : Real.Angle) + c • -normalVector (t : Real.Angle)) +
        inner ℝ ((a • normalVector (t : Real.Angle) + b • tangentVector (t : Real.Angle)) -
          (b • tangentVector (t : Real.Angle) + c • -normalVector (t : Real.Angle)))
          (normalVector (t : Real.Angle)) • normalVector (t : Real.Angle) := by
    simp only [inner_sub_left, inner_add_left, real_inner_smul_left, inner_neg_left, hnn, htn]
    module
  have hv : tangentVector ((t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle)) =
      -normalVector (t : Real.Angle) := by
    ext i
    fin_cases i <;> simp [normalVector, tangentVector, frame,
      Real.Angle.sin_add_pi_div_two, Real.Angle.cos_add_pi_div_two]
  simp only [tangentArmLengths, hy, capVertices, edgeVertices]
  refine ⟨hA _ _ _, hA _ _ _, ?_, ?_⟩ <;>
    simp only [Real.Angle.coe_add, normalVector_add_pi_div_two, hv] <;>
    exact hC _ _ _

theorem surfaceAreaMeasure_atom_length (K : ConvexBody Point) (t : Real.Angle) :
    surfaceAreaMeasure K {t} = Measure.hausdorffMeasure 1 (exposedEdge K t) ∧
    surfaceAreaMeasure K {t} = ENNReal.ofReal (dist (edgeVertices K t).1 (edgeVertices K t).2) ∧
    (edgeVertices K t).1 = (edgeVertices K t).2 +
      (surfaceAreaMeasure K {t}).toReal • tangentVector t := by
  induction t using Real.Angle.induction_on with
  | _ t =>
    have hface : surfaceAreaMeasure K {(t : Real.Angle)} =
        Measure.hausdorffMeasure 1 (exposedEdge K (t : Real.Angle)) := by
      have h := (surfaceAreaMeasure_face_union K).2.2.2.2
        {(t : Real.Angle)} (measurableSet_singleton _) (Or.inr
          ⟨t, t, le_rfl, by linarith [Real.pi_pos], by simp⟩)
      simpa using h
    have hlength : surfaceAreaMeasure K {(t : Real.Angle)} =
        ENNReal.ofReal (dist (edgeVertices K (t : Real.Angle)).1
          (edgeVertices K (t : Real.Angle)).2) := by
      rw [hface, exposedEdge_eq_segment_edgeVertices, hausdorffMeasure_segment,
        edist_dist, dist_comm]
    refine ⟨hface, hlength, ?_⟩
    let S := (fun p ↦ inner ℝ p (tangentVector (t : Real.Angle))) ''
      exposedEdge K (t : Real.Angle)
    have hcompact : IsCompact S := (isCompact_exposedEdge K _).image
      (continuous_id.inner continuous_const)
    have hnonneg : 0 ≤ sSup S - sInf S := sub_nonneg.mpr
      (csInf_le_csSup ((exposedEdge_nonempty K _).image _) hcompact.bddBelow hcompact.bddAbove)
    have hdiff : (edgeVertices K (t : Real.Angle)).1 -
        (edgeVertices K (t : Real.Angle)).2 =
        (sSup S - sInf S) • tangentVector (t : Real.Angle) := by
      simp only [edgeVertices, S]
      module
    have hnorm : ‖tangentVector (t : Real.Angle)‖ = 1 := by
      have h := inner_tangentVector_self t
      rw [real_inner_self_eq_norm_sq] at h
      nlinarith [norm_nonneg (tangentVector (t : Real.Angle))]
    have hdist : dist (edgeVertices K (t : Real.Angle)).1
        (edgeVertices K (t : Real.Angle)).2 = sSup S - sInf S := by
      rw [dist_eq_norm, hdiff, norm_smul, Real.norm_eq_abs, abs_of_nonneg hnonneg,
        hnorm, mul_one]
    rw [hlength, ENNReal.toReal_ofReal dist_nonneg, hdist]
    exact (sub_eq_iff_eq_add.mp hdiff).trans (add_comm _ _)

end MovingSofa
