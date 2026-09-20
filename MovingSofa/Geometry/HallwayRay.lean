import MovingSofa.Geometry.HallwayPartsProperties
import MovingSofa.Geometry.Frame
import MovingSofa.ForMathlib.Geometry.Euclidean.Segment

noncomputable section

open Set MeasureTheory

namespace MovingSofa

/-- Coordinate description of the downward ray of a supporting hallway. -/
theorem mem_rotatingHallwayParts_bRay_iff (s : Set Point) (t : Real.Angle) (p : Point) :
    p ∈ (rotatingHallwayParts s t).bRay ↔
      inner ℝ p (normalVector t) = supportValue s t - 1 ∧
      inner ℝ p (tangentVector t) ≤
        supportValue s (t + ((Real.pi / 2 : ℝ) : Real.Angle)) - 1 := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    change q 0 = 0 ∧ q 1 ≤ 0 at hq
    rw [inner_supportingPlacement_normalVector, inner_supportingPlacement_tangentVector]
    exact ⟨by linarith [hq.1], by linarith [hq.2]⟩
  · intro hp
    obtain ⟨q, rfl⟩ := (show Function.Surjective (supportingPlacement s t) by
      intro p
      obtain ⟨q, hq⟩ := (EuclideanGeometry.o.rotation t).surjective
        (p - (supportValue s t - 1) • normalVector t -
          (supportValue s (t + ((Real.pi / 2 : ℝ) : Real.Angle)) - 1) • tangentVector t)
      refine ⟨q, ?_⟩
      simp only [supportingPlacement, rotationMap, hq]
      abel) p
    rw [inner_supportingPlacement_normalVector, inner_supportingPlacement_tangentVector] at hp
    change supportingPlacement s t q ∈ supportingPlacement s t '' hallwayParts.bRay
    refine ⟨q, ?_, rfl⟩
    change q 0 = 0 ∧ q 1 ≤ 0
    exact ⟨by linarith [hp.1], by linarith [hp.2]⟩

/-- Coordinate description of the leftward ray of a supporting hallway. -/
theorem mem_rotatingHallwayParts_dRay_iff (s : Set Point) (t : Real.Angle) (p : Point) :
    p ∈ (rotatingHallwayParts s t).dRay ↔
      inner ℝ p (normalVector t) ≤ supportValue s t - 1 ∧
      inner ℝ p (tangentVector t) =
        supportValue s (t + ((Real.pi / 2 : ℝ) : Real.Angle)) - 1 := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    change q 0 ≤ 0 ∧ q 1 = 0 at hq
    rw [inner_supportingPlacement_normalVector, inner_supportingPlacement_tangentVector]
    exact ⟨by linarith [hq.1], by linarith [hq.2]⟩
  · intro hp
    obtain ⟨q, rfl⟩ := (show Function.Surjective (supportingPlacement s t) by
      intro p
      obtain ⟨q, hq⟩ := (EuclideanGeometry.o.rotation t).surjective
        (p - (supportValue s t - 1) • normalVector t -
          (supportValue s (t + ((Real.pi / 2 : ℝ) : Real.Angle)) - 1) • tangentVector t)
      refine ⟨q, ?_⟩
      simp only [supportingPlacement, rotationMap, hq]
      abel) p
    rw [inner_supportingPlacement_normalVector, inner_supportingPlacement_tangentVector] at hp
    change supportingPlacement s t q ∈ supportingPlacement s t '' hallwayParts.dRay
    refine ⟨q, ?_, rfl⟩
    change q 0 ≤ 0 ∧ q 1 = 0
    exact ⟨by linarith [hp.1], by linarith [hp.2]⟩

/-- The part of a supporting hallway ray above a transverse line has the expected length. -/
theorem hausdorffMeasure_bRay_inter_normalHalfPlane (s : Set Point) (t u h : ℝ)
    (htrans : 0 < inner ℝ (tangentVector (t : Real.Angle))
      (normalVector (u : Real.Angle))) :
    Measure.hausdorffMeasure 1
        ((rotatingHallwayParts s (t : Real.Angle)).bRay ∩
          normalHalfPlane (u : Real.Angle) h true false) =
      ENNReal.ofReal (max 0
        ((inner ℝ (rotatingHallwayParts s (t : Real.Angle)).innerCorner
          (normalVector (u : Real.Angle)) - h) /
          inner ℝ (tangentVector (t : Real.Angle)) (normalVector (u : Real.Angle)))) := by
  let x := (rotatingHallwayParts s (t : Real.Angle)).innerCorner
  let v := tangentVector (t : Real.Angle)
  let d := inner ℝ v (normalVector (u : Real.Angle))
  let α := (inner ℝ x (normalVector (u : Real.Angle)) - h) / d
  have hd : 0 < d := htrans
  have hxn : inner ℝ x (normalVector (t : Real.Angle)) =
      supportValue s (t : Real.Angle) - 1 := by
    change inner ℝ (supportingPlacement s (t : Real.Angle) (0 : Point))
      (normalVector (t : Real.Angle)) = _
    rw [inner_supportingPlacement_normalVector]
    simp
  have hxt : inner ℝ x v =
      supportValue s ((t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle)) - 1 := by
    change inner ℝ (supportingPlacement s (t : Real.Angle) (0 : Point))
      (tangentVector (t : Real.Angle)) = _
    rw [inner_supportingPlacement_tangentVector]
    simp only [PiLp.zero_apply]
    ring
  have hvn : inner ℝ v (normalVector (t : Real.Angle)) = 0 := by
    rw [real_inner_comm, inner_normalVector_tangentVector]
  have hvv : inner ℝ v v = 1 := inner_tangentVector_self t
  have hpoint (p : Point) (lam : ℝ)
      (hn : inner ℝ p (normalVector (t : Real.Angle)) =
        inner ℝ x (normalVector (t : Real.Angle)))
      (ht : inner ℝ p v = inner ℝ x v - lam) : p = x - lam • v := by
    rw [← inner_normalVector_smul_add_inner_tangentVector_smul p (t : Real.Angle),
      ← inner_normalVector_smul_add_inner_tangentVector_smul x (t : Real.Angle)]
    rw [hn, ht]
    module
  by_cases hα : 0 ≤ α
  · have hset : (rotatingHallwayParts s (t : Real.Angle)).bRay ∩
        normalHalfPlane (u : Real.Angle) h true false = segment ℝ x (x - α • v) := by
      ext p
      change (p ∈ (rotatingHallwayParts s (t : Real.Angle)).bRay ∧
        h ≤ inner ℝ p (normalVector (u : Real.Angle))) ↔ _
      constructor
      · rintro ⟨hray, hu⟩
        rw [mem_rotatingHallwayParts_bRay_iff] at hray
        let lam := inner ℝ x v - inner ℝ p v
        have hlam0 : 0 ≤ lam := by dsimp [lam]; rw [hxt]; linarith [hray.2]
        have hp : p = x - lam • v := by
          apply hpoint p lam
          · rw [hray.1, hxn]
          · dsimp [lam]
            ring
        have hlamα : lam ≤ α := by
          rw [hp, inner_sub_left, real_inner_smul_left] at hu
          apply (le_div_iff₀ hd).2
          dsimp [d]
          nlinarith
        by_cases hα0 : α = 0
        · have : lam = 0 := le_antisymm (hα0 ▸ hlamα) hlam0
          simp [hα0, hp, this]
        · rw [segment_eq_image]
          refine ⟨lam / α,
            ⟨div_nonneg hlam0 hα, (div_le_one (lt_of_le_of_ne hα ?_)).2 hlamα⟩, ?_⟩
          · exact Ne.symm hα0
          · change (1 - lam / α) • x + (lam / α) • (x - α • v) = p
            rw [hp]
            rw [smul_sub, smul_smul, div_mul_cancel₀ _ hα0]
            module
      · intro hp
        rw [segment_eq_image] at hp
        obtain ⟨r, hr, rfl⟩ := hp
        have heq : (1 - r) • x + r • (x - α • v) = x - (r * α) • v := by module
        rw [show (fun θ : ℝ ↦ (1 - θ) • x + θ • (x - α • v)) r =
          x - (r * α) • v from heq]
        constructor
        · rw [mem_rotatingHallwayParts_bRay_iff]
          constructor
          · simp only [inner_sub_left, real_inner_smul_left, hvn, mul_zero, sub_zero, hxn]
          · simp only [inner_sub_left, real_inner_smul_left]
            change inner ℝ x v - r * α * inner ℝ v v ≤ _
            rw [hvv, mul_one, hxt]
            nlinarith [mul_nonneg hr.1 hα]
        · simp only [inner_sub_left, real_inner_smul_left]
          have hrα : r * α ≤ α := by nlinarith [hr.1, hr.2, hα]
          have hαeq : inner ℝ x (normalVector (u : Real.Angle)) - h = α * d := by
            dsimp [α]
            rw [div_mul_cancel₀ _ hd.ne']
          dsimp [d] at hαeq ⊢
          nlinarith
    rw [hset, MeasureTheory.hausdorffMeasure_segment, edist_dist, dist_eq_norm]
    have hvnorm : ‖v‖ = 1 := by
      dsimp [v]
      rw [← sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
      rw [EuclideanSpace.norm_sq_eq]
      simp [tangentVector, frame, Fin.sum_univ_two, Real.sin_sq_add_cos_sq]
    have hsub : x - (x - α • v) = α • v := by module
    rw [hsub, norm_smul, hvnorm, mul_one]
    simp only [Real.norm_eq_abs, abs_of_nonneg hα]
    simp only [x, v, d, α, max_eq_right hα]
  · have hset : (rotatingHallwayParts s (t : Real.Angle)).bRay ∩
        normalHalfPlane (u : Real.Angle) h true false = ∅ := by
      ext p
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hp
      change p ∈ (rotatingHallwayParts s (t : Real.Angle)).bRay ∧
        h ≤ inner ℝ p (normalVector (u : Real.Angle)) at hp
      rw [mem_rotatingHallwayParts_bRay_iff] at hp
      let lam := inner ℝ x v - inner ℝ p v
      have hlam0 : 0 ≤ lam := by dsimp [lam]; rw [hxt]; linarith [hp.1.2]
      have hp' : p = x - lam • v := by
        apply hpoint p lam
        · rw [hp.1.1, hxn]
        · dsimp [lam]
          ring
      have hlamα : lam ≤ α := by
        have hu := hp.2
        rw [hp', inner_sub_left, real_inner_smul_left] at hu
        apply (le_div_iff₀ hd).2
        dsimp [d]
        nlinarith
      linarith
    rw [hset]
    have hα' : α ≤ 0 := le_of_not_ge hα
    simp only [measure_empty, ENNReal.ofReal_zero, x, v, d, α, max_eq_left hα']

/-- A planar set on one line of a moving frame, with bounded tangent coordinate, is short. -/
theorem hausdorffMeasure_le_of_frame_bounds {S : Set Point} {t e lo hi : ℝ}
    (hS : ∀ p ∈ S, inner ℝ p (normalVector (t : Real.Angle)) = e ∧
      lo ≤ inner ℝ p (tangentVector (t : Real.Angle)) ∧
      inner ℝ p (tangentVector (t : Real.Angle)) ≤ hi) :
    Measure.hausdorffMeasure 1 S ≤ ENNReal.ofReal (max 0 (hi - lo)) := by
  have hvv : inner ℝ (tangentVector (t : Real.Angle)) (tangentVector (t : Real.Angle)) = 1 :=
    inner_tangentVector_self t
  have hnorm : ‖tangentVector (t : Real.Angle)‖ = 1 := by
    have h := real_inner_self_eq_norm_mul_norm (tangentVector (t : Real.Angle))
    rw [hvv] at h
    nlinarith [norm_nonneg (tangentVector (t : Real.Angle))]
  have hsub : S ⊆ segment ℝ
      (e • normalVector (t : Real.Angle) + lo • tangentVector (t : Real.Angle))
      (e • normalVector (t : Real.Angle) + max lo hi • tangentVector (t : Real.Angle)) := by
    intro p hp
    obtain ⟨hpn, hplo, hphi⟩ := hS p hp
    obtain ⟨y, hy⟩ : ∃ y : ℝ, inner ℝ p (tangentVector (t : Real.Angle)) = y := ⟨_, rfl⟩
    rw [hy] at hplo hphi
    have hdecomp : p = e • normalVector (t : Real.Angle) + y • tangentVector (t : Real.Angle) := by
      conv_lhs => rw [← inner_normalVector_smul_add_inner_tangentVector_smul p (t : Real.Angle)]
      rw [hpn, hy]
    have hym : y ≤ max lo hi := hphi.trans (le_max_right lo hi)
    rcases le_or_gt (max lo hi) lo with hml | hml
    · have hylo : y = lo := le_antisymm (hym.trans hml) hplo
      rw [hdecomp, hylo]
      exact left_mem_segment ℝ _ _
    · rw [segment_eq_image]
      refine ⟨(y - lo) / (max lo hi - lo),
        ⟨div_nonneg (by linarith) (by linarith), ?_⟩, ?_⟩
      · rw [div_le_one (by linarith)]
        linarith
      · have hθ : lo + (y - lo) / (max lo hi - lo) * (max lo hi - lo) = y := by
          field_simp
          ring
        have hexp : (1 - (y - lo) / (max lo hi - lo)) •
              (e • normalVector (t : Real.Angle) + lo • tangentVector (t : Real.Angle)) +
            ((y - lo) / (max lo hi - lo)) •
              (e • normalVector (t : Real.Angle) +
                max lo hi • tangentVector (t : Real.Angle)) =
            e • normalVector (t : Real.Angle) +
              (lo + (y - lo) / (max lo hi - lo) * (max lo hi - lo)) •
                tangentVector (t : Real.Angle) := by
          module
        show (1 - (y - lo) / (max lo hi - lo)) •
              (e • normalVector (t : Real.Angle) + lo • tangentVector (t : Real.Angle)) +
            ((y - lo) / (max lo hi - lo)) •
              (e • normalVector (t : Real.Angle) +
                max lo hi • tangentVector (t : Real.Angle)) = p
        rw [hexp, hθ]
        exact hdecomp.symm
  refine (measure_mono hsub).trans (le_of_eq ?_)
  rw [MeasureTheory.hausdorffMeasure_segment, edist_dist, dist_eq_norm]
  congr 1
  have hdiff : e • normalVector (t : Real.Angle) + lo • tangentVector (t : Real.Angle) -
      (e • normalVector (t : Real.Angle) + max lo hi • tangentVector (t : Real.Angle)) =
      (lo - max lo hi) • tangentVector (t : Real.Angle) := by module
  rw [hdiff, norm_smul, hnorm, mul_one, Real.norm_eq_abs,
    abs_of_nonpos (sub_nonpos.mpr (le_max_left lo hi)), neg_sub]
  rcases le_total hi lo with hle | hle
  · rw [max_eq_left hle, max_eq_left (by linarith), sub_self]
  · rw [max_eq_right hle, max_eq_right (by linarith)]

end MovingSofa
