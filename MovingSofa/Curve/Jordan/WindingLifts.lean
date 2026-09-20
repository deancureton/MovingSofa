import MovingSofa.Curve.Jordan.WindingLocalConstancy
import MovingSofa.ForMathlib.Topology.Angle
import MovingSofa.Curve.Jordan.WindingConcatenation
import Mathlib.Topology.LocallyConstant.Basic

noncomputable section

open scoped unitInterval

namespace MovingSofa

@[simp] private lemma pointComplex_re (v : Point) : (Complex.orthonormalBasisOneI.repr.symm v).re =
    v 0 := by
  simp [Complex.orthonormalBasisOneI_repr_symm_apply]

@[simp] private lemma pointComplex_im (v : Point) : (Complex.orthonormalBasisOneI.repr.symm v).im =
    v 1 := by
  simp [Complex.orthonormalBasisOneI_repr_symm_apply]

private lemma conj_pointComplex_mul_re (v w : Point) :
    (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm v) *
        Complex.orthonormalBasisOneI.repr.symm w).re = inner ℝ v w := by
  simp [Complex.orthonormalBasisOneI_repr_symm_apply, inner, Fin.sum_univ_two]
  ring

/-- Every continuous interval path avoiding a point admits a continuous angle lift. -/
theorem exists_curveAngleLift_of_avoids {a b : ℝ} (hab : a < b)
    {x : Set.Icc a b → Point} (hx : Continuous x) {p : Point}
    (hp : p ∉ Set.range x) : ∃ α, IsCurveAngleLift x p α := by
  let A : Set.Icc a b := ⟨a, le_rfl, hab.le⟩
  let B : Set.Icc a b := ⟨b, hab.le, le_rfl⟩
  let φ : I → Set.Icc a b := Set.Icc.convexComb A B
  let z : I → ℂ := fun u ↦ Complex.orthonormalBasisOneI.repr.symm (x (φ u) - p)
  have hz : Continuous z :=
    Complex.orthonormalBasisOneI.repr.symm.continuous.comp ((hx.comp (Set.Icc.continuous_convexComb
        A B)).sub
      continuous_const)
  have hzne (u : I) : z u ≠ 0 := by
    rw [← norm_ne_zero_iff, Complex.orthonormalBasisOneI.repr.symm.norm_map, norm_ne_zero_iff,
        sub_ne_zero]
    intro heq
    exact hp ⟨φ u, heq⟩
  let ϑ : I → Real.Angle := fun u ↦ (Complex.arg (z u) : Real.Angle)
  have hϑ : Continuous ϑ := by
    rw [continuous_iff_continuousAt]
    intro u
    exact (Complex.continuousAt_arg_coe_angle (hzne u)).comp hz.continuousAt
  let ϑ₀ := ϑ 0
  obtain ⟨β, hβ, hβ0, hβϑ⟩ := Real.Angle.exists_continuous_lift_zero
    (fun u ↦ ϑ u - ϑ₀) (hϑ.sub continuous_const) (by simp [ϑ₀])
  let ψ : Set.Icc a b → I := fun u ↦
    ⟨((u : ℝ) - a) / (b - a), by
      constructor
      · exact div_nonneg (sub_nonneg.mpr u.property.1) (sub_nonneg.mpr hab.le)
      · exact (div_le_one (sub_pos.mpr hab)).2 (by linarith [u.property.2])⟩
  have hψ : Continuous ψ := by
    apply Continuous.subtype_mk
    fun_prop
  have hφψ (u : Set.Icc a b) : φ (ψ u) = u := by
    apply Subtype.ext
    simp [φ, ψ, A, B]
    field_simp [sub_ne_zero.mpr hab.ne']
    ring
  let c := Complex.arg (z 0)
  refine ⟨fun u ↦ β (ψ u) + c, hβ.comp hψ |>.add continuous_const, fun u ↦ ?_⟩
  have hangle : ((β (ψ u) + c : ℝ) : Real.Angle) = Complex.arg
      (Complex.orthonormalBasisOneI.repr.symm (x u - p)) := by
    rw [Real.Angle.coe_add, hβϑ]
    simp only [ϑ₀, c, ϑ]
    change (Complex.arg (Complex.orthonormalBasisOneI.repr.symm (x (φ (ψ u)) - p)) : Real.Angle) -
        (Complex.arg (z 0) : Real.Angle) + (Complex.arg (z 0) : Real.Angle) = _
    rw [hφψ]
    simp
  have hne : Complex.orthonormalBasisOneI.repr.symm (x u - p) ≠ 0 := by
    rw [← norm_ne_zero_iff, Complex.orthonormalBasisOneI.repr.symm.norm_map, norm_ne_zero_iff,
        sub_ne_zero]
    intro heq
    exact hp ⟨u, heq⟩
  constructor
  · have := congrArg Real.Angle.cos hangle
    rw [Real.Angle.cos_coe, Real.Angle.cos_coe, Complex.cos_arg hne] at this
    simpa only [pointComplex_re, Complex.orthonormalBasisOneI.repr.symm.norm_map] using this
  · have := congrArg Real.Angle.sin hangle
    rw [Real.Angle.sin_coe, Real.Angle.sin_coe, Complex.sin_arg] at this
    simpa only [pointComplex_im, Complex.orthonormalBasisOneI.repr.symm.norm_map] using this

/-- A closed path contained in a strict half-plane about a point has winding zero there. -/
theorem curveWinding_eq_zero_of_inner_pos {a b : ℝ} (hab : a ≤ b)
    {x : Set.Icc a b → Point} (hx : Continuous x)
    (hclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    (p v : Point) (hv : v ≠ 0) (hpos : ∀ u, 0 < inner ℝ v (x u - p)) :
    curveWinding hab x p = 0 := by
  let z := Complex.orthonormalBasisOneI.repr.symm v
  let w := fun u ↦ Complex.orthonormalBasisOneI.repr.symm (x u - p)
  have hz : z ≠ 0 := by
    rw [← norm_ne_zero_iff, Complex.orthonormalBasisOneI.repr.symm.norm_map, norm_ne_zero_iff]
    exact hv
  have hpositive (u : Set.Icc a b) : 0 < (starRingEnd ℂ z * w u).re := by
    rw [conj_pointComplex_mul_re]
    exact hpos u
  have harg : Continuous (fun u ↦ Complex.arg (starRingEnd ℂ z * w u)) :=
    continuous_arg_conj_mul_of_re_pos continuous_const
      (Complex.orthonormalBasisOneI.repr.symm.continuous.comp (hx.sub continuous_const)) hpositive
  let α := fun u ↦ Complex.arg z + Complex.arg (starRingEnd ℂ z * w u)
  have hα : IsCurveAngleLift x p α := by
    refine ⟨continuous_const.add harg, fun u ↦ ?_⟩
    have hw : w u ≠ 0 := by
      intro heq
      simpa [heq] using hpositive u
    simpa only [α, w, pointComplex_re, pointComplex_im,
        Complex.orthonormalBasisOneI.repr.symm.norm_map] using
      normalized_complex_rotation_by_arg hz hw
  rw [hα.curveWinding_eq hab]
  have hend : α ⟨b, hab, le_rfl⟩ = α ⟨a, le_rfl, hab⟩ := by
    simp only [α, w, hclosed]
  rw [hend, sub_self, zero_div]

/-- A closed continuous loop has winding zero at every point of an unbounded connected
component of the complement of its range. -/
theorem curveWinding_eq_zero_of_unbounded_component
    {a b : ℝ} (hab : a ≤ b) {x : Set.Icc a b → Point} (hx : Continuous x)
    (hclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    {p : Point} (hp : p ∉ Set.range x)
    (hunbounded : ¬Bornology.IsBounded (connectedComponentIn (Set.range x)ᶜ p)) :
    curveWinding hab x p = 0 := by
  let V := connectedComponentIn (Set.range x)ᶜ p
  let _ : PreconnectedSpace V :=
    Subtype.preconnectedSpace isPreconnected_connectedComponentIn
  have hlc : IsLocallyConstant (fun z : V ↦ curveWinding hab x z.val) := by
    apply (IsLocallyConstant.iff_exists_open _).mpr
    intro z
    have hzout : z.val ∉ Set.range x := connectedComponentIn_subset _ _ z.property
    obtain ⟨W, hWopen, hzW, hWeq⟩ :=
      curveWinding_locally_constant_off_range hab hx hclosed hzout
    exact ⟨Subtype.val ⁻¹' W, hWopen.preimage continuous_subtype_val, hzW,
      fun z' hz' ↦ hWeq z'.val hz'⟩
  have hrangeBounded : Bornology.IsBounded (Set.range x) := by
    simpa only [Set.image_univ] using (isCompact_univ.image hx).isBounded
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Point)).mp hrangeBounded
  have hRnonneg : 0 ≤ R := by
    have h := hR (Set.mem_range_self ⟨a, le_rfl, hab⟩)
    have hnorm : ‖x ⟨a, le_rfl, hab⟩‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using h
    exact (norm_nonneg _).trans hnorm
  have hvfar : ∃ v ∈ V, R + 1 < ‖v‖ := by
    by_contra hn
    push Not at hn
    apply hunbounded
    refine (Metric.isBounded_iff_subset_closedBall (0 : Point)).2 ⟨R + 1, ?_⟩
    intro v hv
    simpa [Metric.mem_closedBall, dist_zero_right] using hn v hv
  obtain ⟨v, hvV, hvnorm⟩ := hvfar
  have hvzero : curveWinding hab x v = 0 := by
    apply curveWinding_eq_zero_of_inner_pos hab hx hclosed v (-v)
    · exact neg_ne_zero.mpr (by
        intro hv0
        rw [hv0, norm_zero] at hvnorm
        linarith)
    · intro u
      rw [inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq]
      rw [← real_inner_comm v (x u)]
      have hxu := hR (Set.mem_range_self u)
      have hxnorm : ‖x u‖ ≤ R := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hxu
      have hvpos : 0 < ‖v‖ := lt_of_le_of_lt hRnonneg (lt_add_one R) |>.trans hvnorm
      have hvlarge : R < ‖v‖ := lt_trans (lt_add_one R) hvnorm
      have hinner := abs_real_inner_le_norm (x u) v
      have hlower : inner ℝ (x u) v ≤ ‖x u‖ * ‖v‖ := le_trans (le_abs_self _) hinner
      have hprod : ‖x u‖ * ‖v‖ < ‖v‖ * ‖v‖ :=
        lt_of_le_of_lt (mul_le_mul_of_nonneg_right hxnorm (norm_nonneg v))
          (mul_lt_mul_of_pos_right hvlarge hvpos)
      rw [pow_two]
      linarith
  exact (hlc.apply_eq_of_preconnectedSpace ⟨p, mem_connectedComponentIn hp⟩ ⟨v, hvV⟩).trans
    hvzero

end MovingSofa
