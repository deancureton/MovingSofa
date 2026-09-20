import MovingSofa.Analysis.SurfaceMeasure.GraphDefinitions
import MovingSofa.Analysis.SurfaceMeasure.Segment
import MovingSofa.ForMathlib.Convex.Body.Segment
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- A singleton convex body has equal horizontal projection bounds. -/
theorem horizontalBounds_eq_of_subsingleton (K : ConvexBody Point)
    (hK : (K : Set Point).Subsingleton) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) :
    (horizontalBounds K o e).1 = (horizontalBounds K o e).2 := by
  obtain ⟨p, hp⟩ := K.nonempty
  have hset : (K : Set Point) = {p} :=
    Set.eq_singleton_iff_unique_mem.mpr ⟨hp, fun x hx ↦ hK hx hp⟩
  simp [horizontalBounds, horizontalProjection, hset]

/-- Every surface-area integral of a singleton convex body vanishes. -/
theorem surfaceAreaMeasure_integral_eq_zero_of_subsingleton (K : ConvexBody Point)
    (hK : (K : Set Point).Subsingleton) (ψ : Real.Angle → ℝ) :
    (∫ t, ψ t ∂surfaceAreaMeasure K) = 0 := by
  rw [surfaceAreaMeasure_eq_zero_of_subsingleton K hK]
  simp

private theorem horizontalProjection_segment (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) {a b : Point}
    (hK : (K : Set Point) = segment ℝ a b) :
    horizontalProjection K o e = Set.uIcc (e (a - o) 0) (e (b - o) 0) := by
  rw [horizontalProjection, hK, segment_eq_image']
  calc
    (fun p : Point ↦ e (p - o) 0) ''
        ((fun t : ℝ ↦ a + t • (b - a)) '' Set.Icc 0 1) =
        (fun t : ℝ ↦ e (a - o) 0 + t * (e (b - o) 0 - e (a - o) 0)) ''
          Set.Icc 0 1 := by
      rw [Set.image_image]
      congr 1
      funext t
      simp only [map_sub, map_add, map_smul, PiLp.add_apply,
        PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    _ = segment ℝ (e (a - o) 0) (e (b - o) 0) :=
      (segment_eq_image' ℝ (e (a - o) 0) (e (b - o) 0)).symm
    _ = Set.uIcc (e (a - o) 0) (e (b - o) 0) := segment_eq_uIcc _ _

private theorem horizontalBounds_segment (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) {a b : Point}
    (hK : (K : Set Point) = segment ℝ a b) :
    horizontalBounds K o e =
      (min (e (a - o) 0) (e (b - o) 0), max (e (a - o) 0) (e (b - o) 0)) := by
  rw [horizontalBounds, horizontalProjection_segment K o e hK]
  simp [Set.uIcc, csInf_Icc, csSup_Icc]

private theorem coordinate_normal_second_eq_zero_of_horizontalBounds_eq
    (K : ConvexBody Point) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point)
    (d : Point × Point × Real.Angle) (hd : IsSegmentPresentation K d)
    (hbounds : (horizontalBounds K o e).1 = (horizontalBounds K o e).2) :
    e (normalVector d.2.2) 1 = 0 := by
  have hb := horizontalBounds_segment K o e hd.2.1
  rw [hb] at hbounds
  dsimp only at hbounds
  have hx : e (d.1 - o) 0 = e (d.2.1 - o) 0 := by
    have hle₁ := min_le_left (e (d.1 - o) 0) (e (d.2.1 - o) 0)
    have hle₂ := min_le_right (e (d.1 - o) 0) (e (d.2.1 - o) 0)
    have hge₁ := le_max_left (e (d.1 - o) 0) (e (d.2.1 - o) 0)
    have hge₂ := le_max_right (e (d.1 - o) 0) (e (d.2.1 - o) 0)
    linarith
  have hdir0 : e (d.2.1 - d.1) 0 = 0 := by
    simp only [map_sub, PiLp.sub_apply] at hx ⊢
    linarith
  have hdir_ne : e (d.2.1 - d.1) 1 ≠ 0 := by
    intro h
    have hz : d.2.1 - d.1 = 0 := e.injective (by
      simp only [map_zero]
      ext i
      fin_cases i
      · exact hdir0
      · exact h)
    exact hd.1.symm (sub_eq_zero.mp hz)
  have hinner : inner ℝ (e (d.2.1 - d.1)) (e (normalVector d.2.2)) = 0 := by
    rw [e.inner_map_map]
    exact hd.2.2
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_two,
    hdir0, mul_zero, zero_add] at hinner
  exact (mul_eq_zero.mp hinner).resolve_right hdir_ne

/-- A segment with zero horizontal width contributes zero against weights supported on
normals with positive vertical coordinate. -/
theorem segment_integral_eq_zero_of_horizontalBounds_eq
    (K : ConvexBody Point) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point)
    (ψ : Real.Angle → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hsupport : ∀ t, e (normalVector t) 1 < ε → ψ t = 0)
    (d : Point × Point × Real.Angle) (hd : IsSegmentPresentation K d)
    (hbounds : (horizontalBounds K o e).1 = (horizontalBounds K o e).2) :
    (∫ t, ψ t ∂surfaceAreaMeasure K) = 0 := by
  have hn := coordinate_normal_second_eq_zero_of_horizontalBounds_eq K o e d hd hbounds
  have hψn : ψ d.2.2 = 0 := hsupport d.2.2 (by linarith)
  have hnpi : e (normalVector (d.2.2 + (Real.pi : Real.Angle))) 1 = 0 := by
    have hv : normalVector (d.2.2 + (Real.pi : Real.Angle)) = -normalVector d.2.2 := by
      induction d.2.2 using Real.Angle.induction_on with
      | _ t => simpa only [← Real.Angle.coe_add] using normalVector_add_pi t
    rw [hv, map_neg, PiLp.neg_apply, hn, neg_zero]
  have hψnpi : ψ (d.2.2 + (Real.pi : Real.Angle)) = 0 :=
    hsupport _ (by rw [hnpi]; exact hε)
  rw [surfaceAreaMeasure_eq_segmentPresentation K d hd]
  rw [MeasureTheory.integral_smul_measure]
  rw [MeasureTheory.integral_add_measure (MeasureTheory.integrable_dirac (by finiteness))
    (MeasureTheory.integrable_dirac (by finiteness))]
  simp [hψn, hψnpi]

private theorem upperGraphHeight_segment_of_lt (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) {a b : Point}
    (hK : (K : Set Point) = segment ℝ a b)
    (hab : e (a - o) 0 < e (b - o) 0) {x : ℝ}
    (hx : x ∈ Set.Icc (e (a - o) 0) (e (b - o) 0)) :
    upperGraphHeight K o e x = e (a - o) 1 +
      ((x - e (a - o) 0) / (e (b - o) 0 - e (a - o) 0)) *
        (e (b - o) 1 - e (a - o) 1) := by
  let t := (x - e (a - o) 0) / (e (b - o) 0 - e (a - o) 0)
  let y := e (a - o) 1 + t * (e (b - o) 1 - e (a - o) 1)
  have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hab.le)
    · exact (div_le_one (sub_pos.mpr hab)).mpr (by linarith [hx.2])
  have hfiber : {z : ℝ | o + e.symm !₂[x, z] ∈ (K : Set Point)} = {y} := by
    ext z
    rw [Set.mem_ofPred_eq, hK, segment_eq_image', Set.mem_image, Set.mem_singleton_iff]
    constructor
    · rintro ⟨r, hr, heq⟩
      have heq' := congrArg (fun p : Point ↦ e (p - o)) heq
      have heq0 := congrFun (congrArg WithLp.ofLp heq') 0
      have heq1 := congrFun (congrArg WithLp.ofLp heq') 1
      have hrt : r = t := by
        dsimp [t]
        simp only [map_sub, map_add, map_smul, LinearIsometryEquiv.apply_symm_apply,
          PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, Matrix.cons_val_zero,
          smul_eq_mul] at heq0
        simp at heq0
        apply (eq_div_iff (sub_ne_zero.mpr hab.ne')).mpr
        simp only [map_sub, PiLp.sub_apply]
        linarith
      dsimp [y]
      rw [← hrt]
      simp only [map_sub, map_add, map_smul, LinearIsometryEquiv.apply_symm_apply,
          PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, Matrix.cons_val_one,
          smul_eq_mul] at heq1
      simp at heq1
      simp only [map_sub, PiLp.sub_apply]
      linarith
    · intro hzy
      subst z
      refine ⟨t, ht, ?_⟩
      apply e.injective
      ext i
      fin_cases i
      · have hdx : e b 0 - e a 0 ≠ 0 := by
          simp only [map_sub, PiLp.sub_apply] at hab
          linarith
        simp only [map_add, map_sub, LinearIsometryEquiv.apply_symm_apply, map_smul,
          PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
        simp
        dsimp [t]
        simp only [map_sub, PiLp.sub_apply]
        field_simp [hdx]
        ring
      · simp only [map_add, map_sub, LinearIsometryEquiv.apply_symm_apply, map_smul,
          PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
        simp
        dsimp [y]
        simp only [map_sub, PiLp.sub_apply]
        ring
  rw [upperGraphHeight, hfiber, csSup_singleton]

private theorem deriv_upperGraphHeight_segment_of_lt (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) {a b : Point}
    (hK : (K : Set Point) = segment ℝ a b)
    (hab : e (a - o) 0 < e (b - o) 0) {x : ℝ}
    (hx : x ∈ Set.Ioo (e (a - o) 0) (e (b - o) 0)) :
    deriv (upperGraphHeight K o e) x =
      (e (b - o) 1 - e (a - o) 1) / (e (b - o) 0 - e (a - o) 0) := by
  let g : ℝ → ℝ := fun y ↦ e (a - o) 1 +
    ((y - e (a - o) 0) / (e (b - o) 0 - e (a - o) 0)) *
      (e (b - o) 1 - e (a - o) 1)
  have hg : HasDerivAt g
      ((e (b - o) 1 - e (a - o) 1) / (e (b - o) 0 - e (a - o) 0)) x := by
    dsimp [g]
    have hsub : HasDerivAt (fun y : ℝ ↦ y - e (a - o) 0) 1 x :=
      (hasDerivAt_id x).sub_const _
    have hdiv := HasDerivAt.div_const hsub (e (b - o) 0 - e (a - o) 0)
    have hmul := HasDerivAt.mul_const hdiv (e (b - o) 1 - e (a - o) 1)
    convert hmul.const_add (e (a - o) 1) using 1
    all_goals ring
  have heq : upperGraphHeight K o e =ᶠ[nhds x] g := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact upperGraphHeight_segment_of_lt K o e hK hab ⟨hy.1.le, hy.2.le⟩
  exact (hg.congr_of_eventuallyEq heq).deriv

private theorem segment_graph_normal (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) {a b : Point}
    (hab : e (a - o) 0 < e (b - o) 0) :
    let m := (e (b - o) 1 - e (a - o) 1) / (e (b - o) 0 - e (a - o) 0)
    let q := e.symm !₂[-m, 1]
    q ≠ 0 ∧ inner ℝ (b - a) q = 0 ∧
      e (normalVector (vectorNormalAngle q)) 1 = ‖q‖⁻¹ ∧
      dist a b = (e (b - o) 0 - e (a - o) 0) * ‖q‖ := by
  dsimp only
  let m := (e (b - o) 1 - e (a - o) 1) / (e (b - o) 0 - e (a - o) 0)
  let q := e.symm !₂[-m, 1]
  have hq : q ≠ 0 := by
    intro h
    have h1 := congrFun (congrArg WithLp.ofLp (congrArg e h)) 1
    simp [q] at h1
  have hdx : 0 < e (b - o) 0 - e (a - o) 0 := sub_pos.mpr hab
  have hden : e b 0 - e a 0 ≠ 0 := by
    simp only [map_sub, PiLp.sub_apply] at hab
    linarith
  have horth : inner ℝ (b - a) q = 0 := by
    rw [← e.inner_map_map]
    simp only [q, m, LinearIsometryEquiv.apply_symm_apply, PiLp.inner_apply,
      RCLike.inner_apply, conj_trivial, Fin.sum_univ_two, map_sub, PiLp.sub_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp [hden]
    ring
  have hup : e (normalVector (vectorNormalAngle q)) 1 = ‖q‖⁻¹ := by
    rw [normalVector_vectorNormalAngle hq, map_smul, PiLp.smul_apply]
    simp [q]
  have hlen : dist a b = (e (b - o) 0 - e (a - o) 0) * ‖q‖ := by
    rw [dist_eq_norm, ← e.norm_map]
    have hv : e (b - a) = (e (b - o) 0 - e (a - o) 0) • !₂[1, m] := by
      ext i
      fin_cases i
      · simp [m]
      · simp [m]
        field_simp [hden]
    rw [show a - b = -(b - a) by module, map_neg, norm_neg, hv, norm_smul,
      Real.norm_eq_abs, abs_of_pos hdx]
    congr 1
    rw [← e.norm_map q, LinearIsometryEquiv.apply_symm_apply]
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    simp [m, Real.norm_eq_abs, pow_two]
    ring
  exact ⟨hq, horth, hup, hlen⟩

private theorem segment_graph_integrand_ae (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) (ψ : Real.Angle → ℝ) {a b : Point}
    (hK : (K : Set Point) = segment ℝ a b)
    (hab : e (a - o) 0 < e (b - o) 0) :
    let m := (e (b - o) 1 - e (a - o) 1) / (e (b - o) 0 - e (a - o) 0)
    let q := e.symm !₂[-m, 1]
    upperGraphSurfaceIntegrand K o e ψ =ᵐ[
        volume.restrict (Set.Icc (e (a - o) 0) (e (b - o) 0))]
      fun _ ↦ ψ (vectorNormalAngle q) * ‖q‖ := by
  dsimp only
  let m := (e (b - o) 1 - e (a - o) 1) / (e (b - o) 0 - e (a - o) 0)
  let q := e.symm !₂[-m, 1]
  have hnormq : Real.sqrt (1 + m ^ 2) = ‖q‖ := by
    rw [← e.norm_map q, LinearIsometryEquiv.apply_symm_apply, EuclideanSpace.norm_eq]
    congr 1
    simp [Fin.sum_univ_two, Real.norm_eq_abs, pow_two]
    ring
  rw [← restrict_Ioo_eq_restrict_Icc]
  refine ae_restrict_of_forall_mem measurableSet_Ioo fun x hx ↦ ?_
  rw [upperGraphSurfaceIntegrand,
    deriv_upperGraphHeight_segment_of_lt K o e hK hab hx]
  change ψ (vectorNormalAngle q) * Real.sqrt (1 + m ^ 2) = _
  rw [hnormq]

private theorem integrable_segment_graph (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) (ψ : Real.Angle → ℝ) {a b : Point}
    (hK : (K : Set Point) = segment ℝ a b)
    (hab : e (a - o) 0 < e (b - o) 0) :
    Integrable (upperGraphSurfaceIntegrand K o e ψ)
      (volume.restrict (Set.Icc (e (a - o) 0) (e (b - o) 0))) := by
  have hae := segment_graph_integrand_ae K o e ψ hK hab
  have hc : Integrable (fun _ : ℝ ↦ ψ (vectorNormalAngle
      (e.symm !₂[-((e (b - o) 1 - e (a - o) 1) /
        (e (b - o) 0 - e (a - o) 0)), 1])) *
      ‖e.symm !₂[-((e (b - o) 1 - e (a - o) 1) /
        (e (b - o) 0 - e (a - o) 0)), 1]‖)
      (volume.restrict (Set.Icc (e (a - o) 0) (e (b - o) 0))) := integrable_const _
  exact hc.congr hae.symm

private theorem segment_graph_integral (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) (ψ : Real.Angle → ℝ) {a b : Point}
    (hK : (K : Set Point) = segment ℝ a b)
    (hab : e (a - o) 0 < e (b - o) 0) {ε : ℝ} (hε : 0 < ε)
    (hsupport : ∀ t, e (normalVector t) 1 < ε → ψ t = 0) :
    (∫ t, ψ t ∂surfaceAreaMeasure K) =
      ∫ x in Set.Icc (e (a - o) 0) (e (b - o) 0),
        upperGraphSurfaceIntegrand K o e ψ x := by
  let m := (e (b - o) 1 - e (a - o) 1) / (e (b - o) 0 - e (a - o) 0)
  let q := e.symm !₂[-m, 1]
  let t := vectorNormalAngle q
  obtain ⟨hq, horth, hup, hlen⟩ := segment_graph_normal o e hab
  have hd : IsSegmentPresentation K (a, b, t) := by
    refine ⟨?_, hK, ?_⟩
    · intro heq
      have := hab
      simp only at heq
      rw [heq] at this
      exact this.false
    · dsimp [t]
      rw [normalVector_vectorNormalAngle hq, inner_smul_right, horth, mul_zero]
  have hqnorm : 0 < ‖q‖ := norm_pos_iff.mpr hq
  have hdowncoord : e (normalVector (t + (Real.pi : Real.Angle))) 1 = -‖q‖⁻¹ := by
    have hv : normalVector (t + (Real.pi : Real.Angle)) = -normalVector t := by
      induction t using Real.Angle.induction_on with
      | _ t => simpa only [← Real.Angle.coe_add] using normalVector_add_pi t
    rw [hv, map_neg, PiLp.neg_apply]
    exact congrArg Neg.neg hup
  have hdown : ψ (t + (Real.pi : Real.Angle)) = 0 :=
    hsupport _ (by
      rw [hdowncoord]
      have hinv : 0 < ‖q‖⁻¹ := inv_pos.mpr hqnorm
      linarith)
  have hlhs : (∫ u, ψ u ∂surfaceAreaMeasure K) = dist a b * ψ t := by
    rw [surfaceAreaMeasure_eq_segmentPresentation K (a, b, t) hd]
    rw [MeasureTheory.integral_smul_measure]
    rw [MeasureTheory.integral_add_measure (MeasureTheory.integrable_dirac (by finiteness))
      (MeasureTheory.integrable_dirac (by finiteness))]
    simp [hdown, ENNReal.toReal_ofReal (dist_nonneg : 0 ≤ dist a b)]
  rw [hlhs, hlen]
  have hae := segment_graph_integrand_ae K o e ψ hK hab
  rw [integral_congr_ae hae]
  have hdx : 0 ≤ e (b - o) 0 - e (a - o) 0 := sub_nonneg.mpr hab.le
  have hdx' : 0 ≤ e b 0 - e a 0 := by
    simp only [map_sub, PiLp.sub_apply] at hdx
    linarith
  simp [t, q, m]
  rw [max_eq_left hdx']
  ring

/-- The surface-area integral of a nonvertical segment agrees with its upper
graph integral. -/
theorem segment_graph_formula (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) (ψ : Real.Angle → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hsupport : ∀ t, e (normalVector t) 1 < ε → ψ t = 0)
    (d : Point × Point × Real.Angle) (hd : IsSegmentPresentation K d)
    (hbounds : (horizontalBounds K o e).1 < (horizontalBounds K o e).2) :
    Integrable (upperGraphSurfaceIntegrand K o e ψ)
        (volume.restrict (Set.Icc (horizontalBounds K o e).1
          (horizontalBounds K o e).2)) ∧
      (∫ t, ψ t ∂surfaceAreaMeasure K) =
        ∫ x in Set.Icc (horizontalBounds K o e).1 (horizontalBounds K o e).2,
          upperGraphSurfaceIntegrand K o e ψ x := by
  rw [horizontalBounds_segment K o e hd.2.1] at hbounds ⊢
  dsimp only at hbounds ⊢
  have hne : e (d.1 - o) 0 ≠ e (d.2.1 - o) 0 := by
    intro heq
    simp only [map_sub, PiLp.sub_apply] at heq hbounds
    rw [heq, min_self, max_self] at hbounds
    exact hbounds.false
  rcases lt_or_gt_of_ne hne with hab | hba
  · rw [min_eq_left hab.le, max_eq_right hab.le] at hbounds ⊢
    exact ⟨integrable_segment_graph K o e ψ hd.2.1 hbounds,
      segment_graph_integral K o e ψ hd.2.1 hbounds hε hsupport⟩
  · rw [min_eq_right hba.le, max_eq_left hba.le] at hbounds ⊢
    have hK' : (K : Set Point) = segment ℝ d.2.1 d.1 := by
      rw [segment_symm]
      exact hd.2.1
    exact ⟨integrable_segment_graph K o e ψ hK' hbounds,
      segment_graph_integral K o e ψ hK' hbounds hε hsupport⟩

/-- A nonsingleton planar convex body with empty interior has a segment presentation. -/
theorem exists_segmentPresentation_of_interior_empty (K : ConvexBody Point)
    (hsub : ¬(K : Set Point).Subsingleton) (hint : interior (K : Set Point) = ∅) :
    ∃ d, IsSegmentPresentation K d := by
  obtain ⟨a, b, hab, hK⟩ := K.exists_eq_segment_of_interior_empty hsub hint
  let orient : Orientation ℝ Point (Fin 2) :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation
  let _ : Fact (Module.finrank ℝ Point = 2) := ⟨by simp [Point]⟩
  let n := ‖b - a‖⁻¹ • orient.rotation (Real.pi / 2 : ℝ) (b - a)
  have hvnorm : 0 < ‖b - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab.symm)
  have hn : ‖n‖ = 1 := by
    rw [norm_smul, (orient.rotation (Real.pi / 2 : ℝ)).norm_map]
    simp [hvnorm.ne']
  obtain ⟨t, ht⟩ := exists_angle_normalVector_eq hn
  refine ⟨(a, b, t), hab, hK, ?_⟩
  rw [ht]
  exact orient.inner_smul_rotation_pi_div_two_right (b - a) ‖b - a‖⁻¹

end MovingSofa
