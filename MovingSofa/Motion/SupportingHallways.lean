import MovingSofa.Motion.Rotation
import MovingSofa.Convex.Limits
import MovingSofa.Geometry.Parallelogram
import MovingSofa.Motion.Basic
import MovingSofa.Geometry.HallwayPartsProperties

noncomputable section
open Set
open scoped unitInterval
namespace MovingSofa

/-- The supporting placement regarded as an affine isometry equivalence. -/
def supportingPlacementEquiv (s : Set Point) (t : Real.Angle) :
    Point ≃ᵃⁱ[ℝ] Point :=
  (EuclideanGeometry.o.rotation t).toAffineIsometryEquiv.trans
    (AffineIsometryEquiv.vaddConst ℝ
      ((supportValue s t - 1) • normalVector t +
       (supportValue s (t + ((Real.pi / 2 : ℝ) : Real.Angle)) - 1) • tangentVector t))

theorem supportingPlacementEquiv_apply (s : Set Point) (t : Real.Angle) (p : Point) :
    supportingPlacementEquiv s t p = supportingPlacement s t p := by
  simp [supportingPlacementEquiv, supportingPlacement, rotationMap, add_assoc]

private def supportCorner (s : Set Point) (t : Real.Angle) : Point :=
  (supportValue s t - 1) • normalVector t +
    (supportValue s (t + ((Real.pi / 2 : ℝ) : Real.Angle)) - 1) • tangentVector t

private theorem continuous_supportCorner_real (s : Set Point)
    (hs : s.Nonempty) (hc : IsCompact s) :
    Continuous (fun t : ℝ ↦ supportCorner s (t : Real.Angle)) := by
  have hh := (compactSet_support_continuity s s hs hc hs hc).2.2.1
  have hn := continuous_normalVector_real
  have hv : Continuous (fun t : ℝ ↦ tangentVector (t : Real.Angle)) := by
    have h := hn.comp (continuous_id.add (continuous_const (y := Real.pi / 2)))
    simpa only [Function.comp_def, Pi.add_apply, id_eq, Real.Angle.coe_add,
      normalVector_add_pi_div_two] using h
  exact (((hh.comp Real.Angle.continuous_coe).sub continuous_const).smul hn).add
    (((hh.comp (Real.Angle.continuous_coe.add continuous_const)).sub continuous_const).smul hv)

private theorem supportingPlacementEquiv_symm_apply (s : Set Point) (t : Real.Angle)
    (p : Point) :
    (supportingPlacementEquiv s t).symm p =
      ((AffineIsometryEquiv.vaddConst ℝ (-supportCorner s t)).trans
        (EuclideanGeometry.o.rotation (-t)).toAffineIsometryEquiv) p := by
  change (EuclideanGeometry.o.rotation t).symm (p - supportCorner s t) =
    (EuclideanGeometry.o.rotation (-t)) (p + -supportCorner s t)
  simp only [Orientation.rotation_symm_apply, Orientation.rotation_apply,
    Real.Angle.cos_neg, Real.Angle.sin_neg, neg_smul, sub_eq_add_neg]

private theorem continuous_inverse_supportingPlacement (s : Set Point)
    (hs : s.Nonempty) (hc : IsCompact s) :
    Continuous (fun t : ℝ ↦ (supportingPlacementEquiv s (t : Real.Angle)).symm) := by
  have h := continuous_vaddConst_trans_rotation.comp
    (Real.Angle.continuous_coe.neg.prodMk (continuous_supportCorner_real s hs hc).neg)
  apply h.congr
  intro t
  apply AffineIsometryEquiv.ext
  intro p
  exact (supportingPlacementEquiv_symm_apply s (t : Real.Angle) p).symm

private theorem inverse_supportingPlacement_coordinates (s : Set Point)
    (t : Real.Angle) (p : Point) :
    ((supportingPlacementEquiv s t).symm p) 0 =
      inner ℝ p (normalVector t) - supportValue s t + 1 ∧
    ((supportingPlacementEquiv s t).symm p) 1 =
      inner ℝ p (tangentVector t) -
        supportValue s (t + ((Real.pi / 2 : ℝ) : Real.Angle)) + 1 := by
  have hn := inner_supportingPlacement_normalVector s t ((supportingPlacementEquiv s t).symm p)
  have ht := inner_supportingPlacement_tangentVector s t ((supportingPlacementEquiv s t).symm p)
  rw [← supportingPlacementEquiv_apply, AffineIsometryEquiv.apply_symm_apply] at hn ht
  constructor <;> linarith

private theorem inverse_supportingPlacement_mem_hallway (s : Set Point)
    (t : Real.Angle) {p : Point} (hp : p ∈ supportingHallway s t) :
    (supportingPlacementEquiv s t).symm p ∈ hallway := by
  obtain ⟨q, hq, rfl⟩ := hp
  rw [← supportingPlacementEquiv_apply, AffineIsometryEquiv.symm_apply_apply]
  exact hq

private theorem hallway_coordinates_le {p : Point} (hp : p ∈ hallway) :
    p 0 ≤ 1 ∧ p 1 ≤ 1 := by
  rcases hp with ⟨a, b, h, rfl⟩ | ⟨a, b, h, rfl⟩
  · exact ⟨h.1, h.2.2⟩
  · exact ⟨h.2.1, h.2.2⟩

/-- A closed connected subset of the supporting-hallway intersection inherits its
clockwise hallway motion from the reference compact set. -/
theorem hasRotationAngle_of_subset_supportingHallways (s S : Set Point) (ω : ℝ)
    (hsne : s.Nonempty) (hscompact : IsCompact s) (hω : 0 ≤ ω)
    (hsω : supportValue s (ω : Real.Angle) = 1)
    (hsπ : supportValue s ((Real.pi / 2 : ℝ) : Real.Angle) = 1)
    (hSconn : IsConnected S) (hSclosed : IsClosed S)
    (hSsub : S ⊆ monotonization s ω) : HasRotationAngle S ω := by
  let m : I → Point ≃ᵃⁱ[ℝ] Point := fun r ↦
    (supportingPlacementEquiv s ((ω * (r : ℝ) : ℝ) : Real.Angle)).symm
  have hθ (r : I) : ω * (r : ℝ) ∈ Icc (0 : ℝ) ω := by
    exact ⟨mul_nonneg hω r.2.1,
      (mul_le_mul_of_nonneg_left r.2.2 hω).trans_eq (mul_one ω)⟩
  have hall (r : I) : m r '' S ⊆ hallway := by
    rintro p ⟨q, hq, rfl⟩
    apply inverse_supportingPlacement_mem_hallway
    exact mem_iInter.mp (mem_iInter.mp (hSsub hq).2 (ω * (r : ℝ))) (hθ r)
  have hrot (r : I) (p : Point) :
      m r p = rotationMap ((-ω * (r : ℝ) : ℝ) : Real.Angle) p + m r 0 := by
    dsimp [m]
    rw [supportingPlacementEquiv_symm_apply, supportingPlacementEquiv_symm_apply]
    change rotationMap (-((ω * (r : ℝ) : ℝ) : Real.Angle))
      (p + -supportCorner s _) = _
    rw [show ((-ω * (r : ℝ) : ℝ) : Real.Angle) =
      -((ω * (r : ℝ) : ℝ) : Real.Angle) by rw [neg_mul, Real.Angle.coe_neg]]
    simp [rotationMap, map_add]
  refine ⟨m, ?_, (fun r ↦ -ω * (r : ℝ)), by fun_prop, by simp, by simp, hrot⟩
  refine ⟨hSconn,
    hSclosed,
    (continuous_inverse_supportingPlacement s hsne hscompact).comp
      (continuous_const.mul continuous_subtype_val), ?_, ?_, ?_, hall, ?_⟩
  · refine ⟨-supportCorner s 0, ?_⟩
    intro p
    simp [m, supportingPlacementEquiv_symm_apply,
      Orientation.rotation_zero]
  · intro r
    exact ⟨((-ω * (r : ℝ) : ℝ) : Real.Angle), hrot r⟩
  · rintro p ⟨q, hq, rfl⟩
    apply mem_horizontalHallway_of_coordinates
    · exact (hallway_coordinates_le (hall 0 ⟨q, hq, rfl⟩)).1
    · have hc := (inverse_supportingPlacement_coordinates s 0 q).2
      have hqP := (mem_stripParallelogram_iff ω q).mp (hSsub hq).1
      have hy : (m 0 q) 1 = q 1 := by
        simpa [m, hsπ, tangentVector, frame, PiLp.inner_apply,
          Fin.sum_univ_two] using hc
      rw [hy]
      exact hqP.1
  · rintro p ⟨q, hq, rfl⟩
    apply mem_verticalHallway_of_coordinates
    · have hc := (inverse_supportingPlacement_coordinates s (ω : Real.Angle) q).1
      have hqP := (mem_stripParallelogram_iff ω q).mp (hSsub hq).1
      have hx : (m 1 q) 0 = inner ℝ q (normalVector (ω : Real.Angle)) := by
        simpa [m, hsω] using hc
      rw [hx]
      exact hqP.2
    · exact (hallway_coordinates_le (hall 1 ⟨q, hq, rfl⟩)).2

end MovingSofa
