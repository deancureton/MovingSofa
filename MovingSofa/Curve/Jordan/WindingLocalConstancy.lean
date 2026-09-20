import MovingSofa.Curve.Jordan.Winding
import MovingSofa.Geometry.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

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

/-- The principal relative argument varies continuously while the relative dot product is
positive. This is the branch needed for a small displacement of the basepoint. -/
lemma continuous_arg_conj_mul_of_re_pos {α : Type*} [TopologicalSpace α]
    {z w : α → ℂ} (hz : Continuous z) (hw : Continuous w)
    (hpos : ∀ t, 0 < (starRingEnd ℂ (z t) * w t).re) :
    Continuous (fun t ↦ Complex.arg (starRingEnd ℂ (z t) * w t)) := by
  have hf : Continuous (fun u ↦ starRingEnd ℂ (z u) * w u) :=
    (continuous_star.comp hz).mul hw
  change Continuous (Complex.arg ∘ fun u ↦ starRingEnd ℂ (z u) * w u)
  exact Complex.continuousOn_arg.comp_continuous hf (fun t ↦ Or.inl (hpos t))

/-- The principal relative argument rotates the normalized coordinates of `z` to those of `w`. -/
lemma normalized_complex_rotation_by_arg {z w : ℂ}
    (hz : z ≠ 0) (hw : w ≠ 0) :
    Real.cos (Complex.arg z + Complex.arg (starRingEnd ℂ z * w)) = w.re / ‖w‖ ∧
      Real.sin (Complex.arg z + Complex.arg (starRingEnd ℂ z * w)) = w.im / ‖w‖ := by
  have hzw : starRingEnd ℂ z * w ≠ 0 :=
    mul_ne_zero ((map_ne_zero (starRingEnd ℂ)).2 hz) hw
  rw [Real.cos_add, Real.sin_add, Complex.cos_arg hz, Complex.sin_arg,
    Complex.cos_arg hzw, Complex.sin_arg]
  simp only [Complex.norm_mul, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im]
  rw [Complex.norm_conj]
  have hn : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hnz : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  constructor
  · field_simp [hnz]
    linear_combination w.re * hn
  · field_simp [hnz]
    linear_combination w.im * hn

/-- Coordinate form of the preceding rotation identity for any chosen real lift of `z`. -/
lemma normalized_complex_rotation_by_relative_arg {z w : ℂ} {θ : ℝ}
    (hz : z ≠ 0) (hw : w ≠ 0)
    (hc : Real.cos θ = z.re / ‖z‖) (hs : Real.sin θ = z.im / ‖z‖) :
    Real.cos (θ + Complex.arg (starRingEnd ℂ z * w)) = w.re / ‖w‖ ∧
      Real.sin (θ + Complex.arg (starRingEnd ℂ z * w)) = w.im / ‖w‖ := by
  have hzw : starRingEnd ℂ z * w ≠ 0 :=
    mul_ne_zero ((map_ne_zero (starRingEnd ℂ)).2 hz) hw
  rw [Real.cos_add, Real.sin_add, hc, hs, Complex.cos_arg hzw, Complex.sin_arg,
    Complex.norm_mul, Complex.norm_conj]
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  have hn : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hnz : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  constructor
  · field_simp [hnz]
    linear_combination w.re * hn
  · field_simp [hnz]
    linear_combination w.im * hn

/-- A positive relative dot product supplies the continuous principal correction between two
basepoints. -/
lemma IsCurveAngleLift.add_principal_basepoint_correction {a b : ℝ}
    {x : Set.Icc a b → Point} {p q : Point} {θ : Set.Icc a b → ℝ}
    (hx : Continuous x) (hθ : IsCurveAngleLift x p θ)
    (hpos : ∀ u, 0 < (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm (x u - p)) *
      Complex.orthonormalBasisOneI.repr.symm (x u - q)).re) :
    IsCurveAngleLift x q (fun u ↦ θ u +
      Complex.arg (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm (x u - p)) *
          Complex.orthonormalBasisOneI.repr.symm (x u - q))) := by
  let z := fun u ↦ Complex.orthonormalBasisOneI.repr.symm (x u - p)
  let w := fun u ↦ Complex.orthonormalBasisOneI.repr.symm (x u - q)
  have hz : Continuous z := Complex.orthonormalBasisOneI.repr.symm.continuous.comp (hx.sub
      continuous_const)
  have hw : Continuous w := Complex.orthonormalBasisOneI.repr.symm.continuous.comp (hx.sub
      continuous_const)
  have hδ : Continuous (fun u ↦ Complex.arg (starRingEnd ℂ (z u) * w u)) :=
    continuous_arg_conj_mul_of_re_pos hz hw hpos
  refine ⟨hθ.1.add hδ, fun u ↦ ?_⟩
  have hprod : starRingEnd ℂ (z u) * w u ≠ 0 := by
    intro hzero
    have := hpos u
    rw [hzero] at this
    simp at this
  have hzne : z u ≠ 0 := fun hzero ↦ hprod (by simp [hzero])
  have hwne : w u ≠ 0 := fun hzero ↦ hprod (by simp [hzero])
  have hc : Real.cos (θ u) = (z u).re / ‖z u‖ := by
    simpa only [z, pointComplex_re, Complex.orthonormalBasisOneI.repr.symm.norm_map] using (hθ.2
        u).1
  have hs : Real.sin (θ u) = (z u).im / ‖z u‖ := by
    simpa only [z, pointComplex_im, Complex.orthonormalBasisOneI.repr.symm.norm_map] using (hθ.2
        u).2
  simpa only [z, w, pointComplex_re, pointComplex_im,
      Complex.orthonormalBasisOneI.repr.symm.norm_map] using
    normalized_complex_rotation_by_relative_arg hzne hwne hc hs

/-- Moving the basepoint through the positive-relative-dot neighborhood preserves winding. -/
theorem curveWinding_eq_of_relative_dot_pos {a b : ℝ} (hab : a ≤ b)
    {x : Set.Icc a b → Point} (hx : Continuous x)
    (hclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    {p q : Point} {θ : Set.Icc a b → ℝ} (hθ : IsCurveAngleLift x p θ)
    (hpos : ∀ u, 0 < (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm (x u - p)) *
      Complex.orthonormalBasisOneI.repr.symm (x u - q)).re) :
    curveWinding hab x q = curveWinding hab x p := by
  let δ := fun u ↦ Complex.arg (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm (x u - p)) *
    Complex.orthonormalBasisOneI.repr.symm (x u - q))
  have hθδ : IsCurveAngleLift x q (fun u ↦ θ u + δ u) :=
    hθ.add_principal_basepoint_correction hx hpos
  have hδ : δ ⟨a, le_rfl, hab⟩ = δ ⟨b, hab, le_rfl⟩ := by
    simp only [δ, hclosed]
  rw [hθδ.curveWinding_eq hab, hθ.curveWinding_eq hab]
  rw [hδ]
  ring

/-- Off a compact continuous loop, every sufficiently nearby basepoint has positive relative dot
product with the original radial vectors. -/
theorem exists_ball_relative_dot_pos {a b : ℝ} (hab : a ≤ b)
    {x : Set.Icc a b → Point} (hx : Continuous x) {p : Point}
    (hp : p ∉ Set.range x) :
    ∃ r > 0, ∀ q, dist q p < r → ∀ u,
      0 < (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm (x u - p)) *
          Complex.orthonormalBasisOneI.repr.symm (x u - q)).re := by
  let _ : Nonempty (Set.Icc a b) := ⟨⟨a, le_rfl, hab⟩⟩
  let f : Set.Icc a b → ℝ := fun u ↦ ‖x u - p‖
  have hf : Continuous f := (hx.sub continuous_const).norm
  obtain ⟨u₀, -, hu₀⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hf.continuousOn
  have hne (u : Set.Icc a b) : x u - p ≠ 0 := by
    intro hzero
    apply hp
    refine ⟨u, ?_⟩
    exact sub_eq_zero.mp hzero
  have hfu₀ : 0 < f u₀ := norm_pos_iff.mpr (hne u₀)
  refine ⟨f u₀ / 2, half_pos hfu₀, fun q hq u ↦ ?_⟩
  have hmin : f u₀ ≤ f u := hu₀ (Set.mem_univ u)
  have hd : ‖p - q‖ < f u₀ / 2 := by
    simpa [dist_eq_norm, norm_sub_rev] using hq
  have hd' : ‖p - q‖ < ‖x u - p‖ := lt_of_lt_of_le hd (by linarith)
  rw [conj_pointComplex_mul_re]
  have hw : x u - q = (x u - p) + (p - q) := by abel
  rw [hw, inner_add_right, real_inner_self_eq_norm_sq]
  have hcs := abs_real_inner_le_norm (x u - p) (p - q)
  have hlower : -(‖x u - p‖ * ‖p - q‖) ≤ inner ℝ (x u - p) (p - q) :=
    (neg_le_of_abs_le hcs)
  nlinarith [norm_pos_iff.mpr (hne u)]

/-- Winding of a continuous closed loop is locally constant away from its range. -/
theorem curveWinding_locally_constant_off_range {a b : ℝ} (hab : a ≤ b)
    {x : Set.Icc a b → Point} (hx : Continuous x)
    (hclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    {p : Point} (hp : p ∉ Set.range x) :
    ∃ U : Set Point, IsOpen U ∧ p ∈ U ∧
      ∀ q ∈ U, curveWinding hab x q = curveWinding hab x p := by
  obtain ⟨r, hr, hdot⟩ := exists_ball_relative_dot_pos hab hx hp
  refine ⟨Metric.ball p r, Metric.isOpen_ball, Metric.mem_ball_self hr, fun q hq ↦ ?_⟩
  have hqp : dist q p < r := by simpa [dist_comm] using hq
  have hpos := hdot q hqp
  by_cases hpLift : ∃ θ, IsCurveAngleLift x p θ
  · obtain ⟨θ, hθ⟩ := hpLift
    exact curveWinding_eq_of_relative_dot_pos hab hx hclosed hθ hpos
  · have hqLift : ¬∃ ψ, IsCurveAngleLift x q ψ := by
      rintro ⟨ψ, hψ⟩
      have hrev : ∀ u, 0 < (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm (x u - q)) *
          Complex.orthonormalBasisOneI.repr.symm (x u - p)).re := by
        intro u
        rw [conj_pointComplex_mul_re, real_inner_comm, ← conj_pointComplex_mul_re]
        exact hpos u
      exact hpLift ⟨_, hψ.add_principal_basepoint_correction hx hrev⟩
    unfold curveWinding
    rw [dite_eq_right hqLift, dite_eq_right hpLift]

/-- While the relative dot product with the initial radius vector stays positive, the
increment of a continuous angle lift is the principal relative argument, computed as the
arctangent of the ratio of the relative cross product to the relative dot product. -/
theorem IsCurveAngleLift.sub_eq_arctan_of_dot_pos {a b : ℝ}
    {x : Set.Icc a b → Point} {p : Point} {θ : Set.Icc a b → ℝ}
    (hx : Continuous x) (hθ : IsCurveAngleLift x p θ) {t u : Set.Icc a b}
    (htu : (t : ℝ) ≤ (u : ℝ))
    (hpos : ∀ s : Set.Icc a b, (t : ℝ) ≤ (s : ℝ) → (s : ℝ) ≤ (u : ℝ) →
      0 < (x t - p) 0 * (x s - p) 0 + (x t - p) 1 * (x s - p) 1) :
    θ u - θ t = Real.arctan
      (((x t - p) 0 * (x u - p) 1 - (x t - p) 1 * (x u - p) 0) /
        ((x t - p) 0 * (x u - p) 0 + (x t - p) 1 * (x u - p) 1)) := by
  have hsub : ∀ s : Set.Icc (t : ℝ) (u : ℝ), (s : ℝ) ∈ Set.Icc a b := fun s ↦
    ⟨le_trans t.property.1 s.property.1, le_trans s.property.2 u.property.2⟩
  let ι : Set.Icc (t : ℝ) (u : ℝ) → Set.Icc a b := fun s ↦ ⟨s.val, hsub s⟩
  have hι : Continuous ι := continuous_subtype_val.subtype_mk _
  set y : Set.Icc (t : ℝ) (u : ℝ) → Point := x ∘ ι with hy
  have hycont : Continuous y := hx.comp hι
  have hιu : ι ⟨(u : ℝ), htu, le_rfl⟩ = u := Subtype.ext rfl
  have hιt : ι ⟨(t : ℝ), le_rfl, htu⟩ = t := Subtype.ext rfl
  set z : ℂ := Complex.orthonormalBasisOneI.repr.symm (x t - p) with hz
  set w : Set.Icc (t : ℝ) (u : ℝ) → ℂ :=
    fun s ↦ Complex.orthonormalBasisOneI.repr.symm (y s - p) with hw
  have hwcont : Continuous w :=
    Complex.orthonormalBasisOneI.repr.symm.continuous.comp (hycont.sub continuous_const)
  have hre (s : Set.Icc (t : ℝ) (u : ℝ)) :
      (starRingEnd ℂ z * w s).re =
        (x t - p) 0 * (x (ι s) - p) 0 + (x t - p) 1 * (x (ι s) - p) 1 := by
    simp only [hz, hw, hy, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      pointComplex_re, pointComplex_im, Function.comp_apply]
    ring
  have him (s : Set.Icc (t : ℝ) (u : ℝ)) :
      (starRingEnd ℂ z * w s).im =
        (x t - p) 0 * (x (ι s) - p) 1 - (x t - p) 1 * (x (ι s) - p) 0 := by
    simp only [hz, hw, hy, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      pointComplex_re, pointComplex_im, Function.comp_apply]
    ring
  have hposC : ∀ s : Set.Icc (t : ℝ) (u : ℝ), 0 < (starRingEnd ℂ z * w s).re := by
    intro s
    rw [hre s]
    exact hpos (ι s) s.property.1 s.property.2
  have hzne : z ≠ 0 := by
    intro h0
    have := hposC ⟨(t : ℝ), le_rfl, htu⟩
    rw [h0] at this
    simp at this
  have hwne : ∀ s, w s ≠ 0 := by
    intro s h0
    have := hposC s
    rw [h0] at this
    simp at this
  have hznorm : ‖z‖ = ‖x t - p‖ := Complex.orthonormalBasisOneI.repr.symm.norm_map _
  have hc : Real.cos (θ t) = z.re / ‖z‖ := by
    rw [hznorm, hz, pointComplex_re]; exact (hθ.2 t).1
  have hsn : Real.sin (θ t) = z.im / ‖z‖ := by
    rw [hznorm, hz, pointComplex_im]; exact (hθ.2 t).2
  have hlift1 : IsCurveAngleLift y p (θ ∘ ι) := hθ.comp hι
  have hlift2 : IsCurveAngleLift y p
      (fun s ↦ θ t + Complex.arg (starRingEnd ℂ z * w s)) := by
    refine ⟨continuous_const.add
      (continuous_arg_conj_mul_of_re_pos continuous_const hwcont hposC), fun s ↦ ?_⟩
    have hrot := normalized_complex_rotation_by_relative_arg hzne (hwne s) hc hsn
    have hwnorm : ‖w s‖ = ‖y s - p‖ :=
      Complex.orthonormalBasisOneI.repr.symm.norm_map _
    rw [hwnorm] at hrot
    simpa only [hw, pointComplex_re, pointComplex_im] using hrot
  have hincr := IsCurveAngleLift.endpoint_increment_eq htu hlift1 hlift2
  simp only [Function.comp_apply, hιu, hιt] at hincr
  have hwt : w ⟨(t : ℝ), le_rfl, htu⟩ = z := by
    simp only [hw, hy, Function.comp_apply, hιt, hz]
  have hargt : Complex.arg (starRingEnd ℂ z * w ⟨(t : ℝ), le_rfl, htu⟩) = 0 := by
    rw [hwt, mul_comm, Complex.mul_conj]
    exact Complex.arg_ofReal_of_nonneg (Complex.normSq_nonneg z)
  rw [hargt] at hincr
  have hre' : (starRingEnd ℂ z * w ⟨(u : ℝ), htu, le_rfl⟩).re =
      (x t - p) 0 * (x u - p) 0 + (x t - p) 1 * (x u - p) 1 := by
    rw [hre ⟨(u : ℝ), htu, le_rfl⟩, hιu]
  have him' : (starRingEnd ℂ z * w ⟨(u : ℝ), htu, le_rfl⟩).im =
      (x t - p) 0 * (x u - p) 1 - (x t - p) 1 * (x u - p) 0 := by
    rw [him ⟨(u : ℝ), htu, le_rfl⟩, hιu]
  have hargu : Complex.arg (starRingEnd ℂ z * w ⟨(u : ℝ), htu, le_rfl⟩) =
      Real.arctan
        (((x t - p) 0 * (x u - p) 1 - (x t - p) 1 * (x u - p) 0) /
          ((x t - p) 0 * (x u - p) 0 + (x t - p) 1 * (x u - p) 1)) := by
    rw [← hre', ← him']
    have hlt : |Complex.arg (starRingEnd ℂ z * w ⟨(u : ℝ), htu, le_rfl⟩)| < Real.pi / 2 :=
      Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (hposC _))
    refine (Real.arctan_eq_of_tan_eq (Complex.tan_arg _) ?_).symm
    exact ⟨neg_lt_of_abs_lt hlt, lt_of_abs_lt hlt⟩
  rw [hargu] at hincr
  linarith [hincr]

/-- Winding is constant on an open neighbourhood of any point off the range of a closed
continuous loop, and that neighbourhood avoids the range. -/
theorem curveWinding_locally_constant_on_compl_range
    {a b : ℝ} (hab : a ≤ b) {x : Set.Icc a b → Point} (hx : Continuous x)
    (hclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    {p : Point} (hp : p ∉ Set.range x) :
    ∃ U : Set Point, IsOpen U ∧ p ∈ U ∧ ∀ q ∈ U,
      q ∉ Set.range x ∧ curveWinding hab x q = curveWinding hab x p := by
  obtain ⟨U, hU, hpU, heq⟩ := curveWinding_locally_constant_off_range hab hx hclosed hp
  have hclosedRange : IsClosed (Set.range x) := by
    simpa only [Set.image_univ] using (isCompact_univ.image hx).isClosed
  exact ⟨U ∩ (Set.range x)ᶜ, hU.inter hclosedRange.isOpen_compl, ⟨hpU, hp⟩,
    fun q hq ↦ ⟨hq.2, heq q hq.1⟩⟩

end MovingSofa
