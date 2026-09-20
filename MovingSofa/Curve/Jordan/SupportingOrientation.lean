import MovingSofa.Curve.Jordan.WindingLifts
import MovingSofa.Curve.Jordan.Separation
import MovingSofa.Geometry.Frame

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

private theorem continuous_arg_comp_of_re_nonneg {A : Type*} [TopologicalSpace A]
    {z : A → ℂ} (hz : Continuous z) (hre : ∀ u, 0 ≤ (z u).re) (hne : ∀ u, z u ≠ 0) :
    Continuous (fun u ↦ Complex.arg (z u)) := by
  rw [continuous_iff_continuousAt]
  intro u
  have hmem : z u ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff_arg]
    constructor
    · intro harg
      have hneg := (Complex.arg_eq_pi_iff.mp harg).1
      linarith [hre u]
    · exact hne u
  exact (Complex.continuousAt_arg hmem).comp_of_eq hz.continuousAt rfl

private def frameComplex (t : Real.Angle) (v : Point) : ℂ :=
  inner ℝ v (normalVector t) + inner ℝ v (tangentVector t) * Complex.I

@[simp] private theorem frameComplex_re (t : Real.Angle) (v : Point) :
    (frameComplex t v).re = inner ℝ v (normalVector t) := by
  simp [frameComplex]

@[simp] private theorem frameComplex_im (t : Real.Angle) (v : Point) :
    (frameComplex t v).im = inner ℝ v (tangentVector t) := by
  simp [frameComplex]

private theorem norm_frameComplex (t : Real.Angle) (v : Point) :
    ‖frameComplex t v‖ = ‖v‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp [frameComplex, Complex.sq_norm, Complex.normSq_apply, EuclideanSpace.norm_sq_eq,
    normalVector, tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
  ring_nf
  linear_combination (v 0 ^ 2 + v 1 ^ 2) * t.cos_sq_add_sin_sq

private theorem conj_pointComplex_mul_eq_conj_frameComplex_mul (t : Real.Angle)
    (v w : Point) :
    starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm v) *
        Complex.orthonormalBasisOneI.repr.symm w =
      starRingEnd ℂ (frameComplex t v) * frameComplex t w := by
  apply Complex.ext <;>
    simp [Complex.orthonormalBasisOneI_repr_symm_apply, frameComplex, normalVector, tangentVector,
        frame,
      PiLp.inner_apply, Fin.sum_univ_two] <;> ring_nf
  · linear_combination -(v 0 * w 0 + v 1 * w 1) * t.cos_sq_add_sin_sq
  · linear_combination -(v 0 * w 1 - v 1 * w 0) * t.cos_sq_add_sin_sq

private theorem frameComplex_ne_zero {t : Real.Angle} {v : Point} (hv : v ≠ 0) :
    frameComplex t v ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_frameComplex, norm_ne_zero_iff]
  exact hv

private theorem normalized_frameComplex_arg (t : Real.Angle) (v : Point) (hv : v ≠ 0) :
    Real.cos (t.toReal + Complex.arg (frameComplex t v)) = v 0 / ‖v‖ ∧
      Real.sin (t.toReal + Complex.arg (frameComplex t v)) = v 1 / ‖v‖ := by
  have hf := frameComplex_ne_zero (t := t) hv
  rw [Real.cos_add, Real.sin_add, Complex.cos_arg hf, Complex.sin_arg,
    norm_frameComplex]
  simp [frameComplex, normalVector, tangentVector, frame, PiLp.inner_apply,
    Fin.sum_univ_two]
  constructor
  · field_simp
    ring_nf
    linear_combination (v 0) * t.cos_sq_add_sin_sq
  · field_simp
    ring_nf
    linear_combination (v 1) * t.cos_sq_add_sin_sq

/-- The frame argument gives an angle lift when a path lies on the nonnegative side of a normal
through its basepoint. -/
private theorem isCurveAngleLift_frameArg_of_inner_nonneg {a b : ℝ}
    {x : Set.Icc a b → Point} {p : Point} (t : Real.Angle)
    (hx : Continuous x) (hre : ∀ u, 0 ≤ inner ℝ (x u - p) (normalVector t))
    (hne : ∀ u, x u ≠ p) :
    IsCurveAngleLift x p
      (fun u ↦ t.toReal + Complex.arg (frameComplex t (x u - p))) := by
  have hz : Continuous (fun u ↦ frameComplex t (x u - p)) := by
    unfold frameComplex
    fun_prop
  have hzne (u) : frameComplex t (x u - p) ≠ 0 :=
    frameComplex_ne_zero (sub_ne_zero.mpr (hne u))
  refine ⟨continuous_const.add (continuous_arg_comp_of_re_nonneg hz
    (fun u ↦ by simpa using hre u) hzne),
    fun u ↦ ?_⟩
  exact normalized_frameComplex_arg t (x u - p) (sub_ne_zero.mpr (hne u))

/-- Negating frame coordinates and adding `π` gives the corresponding lift on the nonpositive
side of a normal through the basepoint. -/
private theorem isCurveAngleLift_frameArg_neg_add_pi_of_inner_nonpos {a b : ℝ}
    {x : Set.Icc a b → Point} {p : Point} (t : Real.Angle)
    (hx : Continuous x) (hre : ∀ u, inner ℝ (x u - p) (normalVector t) ≤ 0)
    (hne : ∀ u, x u ≠ p) :
    IsCurveAngleLift x p (fun u ↦
      t.toReal + Complex.arg (-frameComplex t (x u - p)) + Real.pi) := by
  have hz : Continuous (fun u ↦ -frameComplex t (x u - p)) := by
    unfold frameComplex
    fun_prop
  have hzne (u) : frameComplex t (x u - p) ≠ 0 :=
    frameComplex_ne_zero (sub_ne_zero.mpr (hne u))
  have harg : Continuous (fun u ↦ Complex.arg (-frameComplex t (x u - p))) :=
    continuous_arg_comp_of_re_nonneg hz (by
      intro u
      simpa using neg_nonneg.mpr (hre u)) (fun u ↦ neg_ne_zero.mpr (hzne u))
  refine ⟨(continuous_const.add harg).add continuous_const, fun u ↦ ?_⟩
  have hbase := normalized_frameComplex_arg t (x u - p) (sub_ne_zero.mpr (hne u))
  have hneg :
      Real.cos (Complex.arg (-frameComplex t (x u - p)) + Real.pi) =
          (frameComplex t (x u - p)).re / ‖frameComplex t (x u - p)‖ ∧
        Real.sin (Complex.arg (-frameComplex t (x u - p)) + Real.pi) =
          (frameComplex t (x u - p)).im / ‖frameComplex t (x u - p)‖ := by
    rw [Real.cos_add_pi, Real.sin_add_pi,
      Complex.cos_arg (neg_ne_zero.mpr (hzne u)), Complex.sin_arg, norm_neg]
    simp only [Complex.neg_re, Complex.neg_im, neg_div, neg_neg]
    exact ⟨trivial, trivial⟩
  dsimp only
  rw [add_assoc, Real.cos_add t.toReal, Real.sin_add t.toReal, hneg.1, hneg.2,
    norm_frameComplex]
  rw [Real.cos_add, Real.sin_add, Complex.cos_arg (hzne u), Complex.sin_arg,
    norm_frameComplex] at hbase
  exact hbase

private def cyclicComplement {a b : ℝ} (hab : a ≤ b) (x : Set.Icc a b → Point)
    (s t : Set.Icc a b) : Set.Icc (0 : ℝ) 2 → Point :=
  Function.concatUnitIntervals
    (x ∘ Set.Icc.convexComb t ⟨b, hab, le_rfl⟩)
    (x ∘ Set.Icc.convexComb ⟨a, le_rfl, hab⟩ s)

private theorem continuous_cyclicComplement {a b : ℝ} (hab : a ≤ b)
    {x : Set.Icc a b → Point} (hx : Continuous x)
    (hclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    (s t : Set.Icc a b) : Continuous (cyclicComplement hab x s t) := by
  apply Function.continuous_concatUnitIntervals
  · exact hx.comp (Set.Icc.continuous_convexComb _ _)
  · exact hx.comp (Set.Icc.continuous_convexComb _ _)
  · simpa [Function.comp_apply] using hclosed.symm

@[simp] private theorem cyclicComplement_zero {a b : ℝ} (hab : a ≤ b)
    (x : Set.Icc a b → Point) (s t : Set.Icc a b) :
    cyclicComplement hab x s t ⟨0, by norm_num⟩ = x t := by
  simp [cyclicComplement]

@[simp] private theorem cyclicComplement_two {a b : ℝ} (hab : a ≤ b)
    (x : Set.Icc a b → Point) (s t : Set.Icc a b) :
    cyclicComplement hab x s t ⟨2, by norm_num⟩ = x s := by
  simp [cyclicComplement]

private theorem tangentVector_ne_zero (t : Real.Angle) : tangentVector t ≠ 0 := by
  intro h
  have hone : inner ℝ (tangentVector t) (tangentVector t) = 1 := by
    rw [← t.coe_toReal]
    exact inner_tangentVector_self t.toReal
  rw [h] at hone
  simp at hone

private theorem convexComb_between {a b : ℝ} {l u : Set.Icc a b} (hlu : l ≤ u)
    (r : Set.Icc (0 : ℝ) 1) :
    l ≤ Set.Icc.convexComb l u r ∧ Set.Icc.convexComb l u r ≤ u := by
  change (l : ℝ) ≤ (1 - (r : ℝ)) * l + (r : ℝ) * u ∧
    (1 - (r : ℝ)) * l + (r : ℝ) * u ≤ u
  constructor <;> nlinarith [r.property.1, r.property.2, show (l : ℝ) ≤ u from hlu]

private theorem range_comp_convexComb {a b : ℝ} {l u : Set.Icc a b} (hlu : l ≤ u)
    (x : Set.Icc a b → Point) :
    Set.range (x ∘ Set.Icc.convexComb l u) = x '' Set.Icc l u := by
  by_cases heq : l = u
  · subst u
    simp [Set.Icc_self]
  have hneval : (l : ℝ) ≠ (u : ℝ) := fun h ↦ heq (Subtype.ext h)
  have hlt : (l : ℝ) < (u : ℝ) := lt_of_le_of_ne hlu hneval
  ext p
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨_, convexComb_between hlu r, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    let r : I := ⟨((v : ℝ) - l) / ((u : ℝ) - l), by
      constructor
      · exact div_nonneg (sub_nonneg.mpr hv.1)
          (sub_nonneg.mpr (show (l : ℝ) ≤ u from hlu))
      · exact (div_le_one (sub_pos.mpr hlt)).2
          (by
            have hv₂ : (v : ℝ) ≤ (u : ℝ) := hv.2
            linarith)⟩
    refine ⟨r, congrArg x ?_⟩
    apply Subtype.ext
    simp [r]
    field_simp [sub_ne_zero.mpr hlt.ne']
    ring

private theorem inner_eq_of_mem_segment {P Q z v : Point} {c : ℝ}
    (hP : inner ℝ P v = c) (hQ : inner ℝ Q v = c)
    (hz : z ∈ segment ℝ P Q) : inner ℝ z v = c := by
  rw [segment_eq_image] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, hP, hQ]
  nlinarith [hr.1, hr.2]

private theorem arg_conj_I_mul_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    Complex.arg (starRingEnd ℂ Complex.I * z) = Complex.arg z - Real.pi / 2 := by
  have hzne : z ≠ 0 := fun h ↦ by simp [h] at hz
  have harg := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  rw [Complex.arg_mul (by simp) hzne]
  · simp only [Complex.conj_I, Complex.arg_neg_I]
    ring
  · simp only [Complex.conj_I, Complex.arg_neg_I]
    constructor <;> have h := abs_lt.mp harg <;> linarith [Real.pi_pos]

private theorem arg_conj_neg_I_mul_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    Complex.arg (starRingEnd ℂ (-Complex.I) * z) = Complex.arg z + Real.pi / 2 := by
  have hzne : z ≠ 0 := fun h ↦ by simp [h] at hz
  have harg := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  rw [Complex.arg_mul (by simp) hzne]
  · simp only [map_neg, Complex.conj_I, neg_neg, Complex.arg_I]
    ring
  · simp only [map_neg, Complex.conj_I, neg_neg, Complex.arg_I]
    constructor <;> have h := abs_lt.mp harg <;> linarith [Real.pi_pos]

private theorem relative_arg_of_frame_eq_pos_I {t : Real.Angle} {v w : Point}
    {D : ℝ} (hD : 0 < D) (hv : frameComplex t v = (D : ℂ) * Complex.I)
    (hw : 0 < (frameComplex t w).re) :
    Complex.arg (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm v) *
        Complex.orthonormalBasisOneI.repr.symm w) =
      Complex.arg (frameComplex t w) - Real.pi / 2 := by
  rw [conj_pointComplex_mul_eq_conj_frameComplex_mul, hv]
  have heq : starRingEnd ℂ ((D : ℂ) * Complex.I) * frameComplex t w =
      (D : ℂ) * (starRingEnd ℂ Complex.I * frameComplex t w) := by
    simp [mul_assoc]
  rw [heq, Complex.arg_real_mul _ hD]
  exact arg_conj_I_mul_of_re_pos hw

private theorem relative_arg_of_frame_eq_neg_I {t : Real.Angle} {v w : Point}
    {D : ℝ} (hD : 0 < D) (hv : frameComplex t v = -(D : ℂ) * Complex.I)
    (hw : 0 < (frameComplex t w).re) :
    Complex.arg (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm v) *
        Complex.orthonormalBasisOneI.repr.symm w) =
      Complex.arg (frameComplex t w) + Real.pi / 2 := by
  rw [conj_pointComplex_mul_eq_conj_frameComplex_mul, hv]
  have heq : starRingEnd ℂ (-(D : ℂ) * Complex.I) * frameComplex t w =
      (D : ℂ) * (starRingEnd ℂ (-Complex.I) * frameComplex t w) := by
    simp [mul_assoc]
  rw [heq, Complex.arg_real_mul _ hD]
  exact arg_conj_neg_I_mul_of_re_pos hw

/-- The midpoint of a nontrivial segment traversed on `[s,t]` is avoided by the cyclic
complementary path. -/
private theorem cyclicComplement_ne_midpoint {a b : ℝ} (hab : a < b)
    {x : Set.Icc a b → Point}
    (hclosed : x ⟨a, le_rfl, hab.le⟩ = x ⟨b, hab.le, le_rfl⟩)
    (hinj : Set.InjOn x {u | (u : ℝ) < b})
    (s t : Set.Icc a b) (hst : s < t) (hxt : x s ≠ x t)
    (hsegment : x '' Set.Icc s t = segment ℝ (x s) (x t)) :
    ∀ u, cyclicComplement hab.le x s t u ≠ midpoint ℝ (x s) (x t) := by
  have hmseg : midpoint ℝ (x s) (x t) ∈ x '' Set.Icc s t := by
    rw [hsegment]
    exact midpoint_mem_segment _ _
  obtain ⟨v, hvst, hv⟩ := hmseg
  have hmvP : midpoint ℝ (x s) (x t) ≠ x s := by
    intro hm
    exact hxt ((midpoint_eq_left_iff ℝ).mp hm)
  have hmvQ : midpoint ℝ (x s) (x t) ≠ x t := by
    intro hm
    exact hxt ((midpoint_eq_right_iff ℝ).mp hm)
  have hsv : s < v := lt_of_le_of_ne hvst.1 (fun h ↦ hmvP (hv ▸ congrArg x h.symm))
  have hvt : v < t := lt_of_le_of_ne hvst.2 (fun h ↦ hmvQ (hv ▸ congrArg x h))
  have hsv' : (s : ℝ) < v := hsv
  have hvt' : (v : ℝ) < t := hvt
  have hvb : (v : ℝ) < b := lt_of_lt_of_le hvt t.property.2
  intro u hu
  have heval :
      (x ∘ Set.Icc.convexComb t ⟨b, hab.le, le_rfl⟩)
          (Set.projIcc 0 1 (by norm_num) (u : ℝ)) =
          midpoint ℝ (x s) (x t) ∨
        (x ∘ Set.Icc.convexComb ⟨a, le_rfl, hab.le⟩ s)
            (Set.projIcc 0 1 (by norm_num) ((u : ℝ) - 1)) =
              midpoint ℝ (x s) (x t) := by
    unfold cyclicComplement Function.concatUnitIntervals at hu
    split_ifs at hu with h
    · exact Or.inl hu
    · exact Or.inr hu
  rcases heval with htail | hhead
  · let w := Set.Icc.convexComb t ⟨b, hab.le, le_rfl⟩
      (Set.projIcc 0 1 (by norm_num) (u : ℝ))
    have htw : t ≤ w := (convexComb_between t.property.2 _).1
    have hxwv : x w = x v := htail.trans hv.symm
    by_cases hwb : (w : ℝ) = b
    · have hwtop : w = (⟨b, hab.le, le_rfl⟩ : Set.Icc a b) := Subtype.ext hwb
      have hxav : x ⟨a, le_rfl, hab.le⟩ = x v := hclosed.trans (hwtop ▸ hxwv)
      have hav := hinj (by simp [hab]) (by exact hvb) hxav
      have hav' := congrArg Subtype.val hav
      linarith [s.property.1]
    · have hwb' : (w : ℝ) < b := lt_of_le_of_ne w.property.2 hwb
      have hwv := hinj hwb' hvb hxwv
      have hwv' := congrArg Subtype.val hwv
      have htw' : (t : ℝ) ≤ w := htw
      linarith
  · let w := Set.Icc.convexComb ⟨a, le_rfl, hab.le⟩ s
      (Set.projIcc 0 1 (by norm_num) ((u : ℝ) - 1))
    have hws : w ≤ s := (convexComb_between s.property.1 _).2
    have hxwv : x w = x v := hhead.trans hv.symm
    have hwb : (w : ℝ) < b := lt_of_le_of_lt hws (lt_of_lt_of_le hst t.property.2)
    have hwv := hinj hwb hvb hxwv
    have hwv' := congrArg Subtype.val hwv
    have hws' : (w : ℝ) ≤ s := hws
    linarith

theorem jordan_counterclockwise_of_supporting_segment
    (a b : ℝ) (hab : a < b) (x : Set.Icc a b → Point)
    (hx : Continuous x) (hΓ : IsJordanCurve (Set.range x))
    (hclosed : x ⟨a, le_rfl, hab.le⟩ = x ⟨b, hab.le, le_rfl⟩)
    (hinj : Set.InjOn x {t | (t : ℝ) < b})
    (θ : Real.Angle) (h : ℝ)
    (hhalf : ∀ t, x t ∈ normalHalfPlane θ h false false)
    (s t : Set.Icc a b) (hst : s < t)
    (hline : x s ∈ normalLine θ h)
    (d : ℝ) (hd : 0 < d) (hdirection : x t = x s + d • tangentVector θ)
    (hsegment : x '' Set.Icc s t = segment ℝ (x s) (x t)) :
    IsOrientedJordanParametrization hab.le (Set.range x) true x := by
  have hxt : x s ≠ x t := by
    intro heq
    have hz : d • tangentVector θ = 0 := by
      calc
        d • tangentVector θ = x t - x s := by rw [hdirection]; abel
        _ = 0 := by rw [← heq, sub_self]
    exact tangentVector_ne_zero θ ((smul_eq_zero.mp hz).resolve_left hd.ne')
  let m := midpoint ℝ (x s) (x t)
  let y := cyclicComplement hab.le x s t
  have hy : Continuous y := continuous_cyclicComplement hab.le hx hclosed s t
  have hym (u : Set.Icc (0 : ℝ) 2) : y u ≠ m := by
    exact cyclicComplement_ne_midpoint hab hclosed hinj s t hst hxt hsegment u
  obtain ⟨r, hr, hdot⟩ := exists_ball_relative_dot_pos (by norm_num) hy (by
    intro hm
    obtain ⟨u, hu⟩ := hm
    exact hym u hu)
  have hxsN : inner ℝ (x s) (normalVector θ) = h := hline
  have htn : inner ℝ (tangentVector θ) (normalVector θ) = 0 := by
    rw [← θ.coe_toReal, real_inner_comm]
    exact inner_normalVector_tangentVector θ.toReal
  have hxtN : inner ℝ (x t) (normalVector θ) = h := by
    rw [hdirection, inner_add_left, real_inner_smul_left, hxsN, htn, mul_zero, add_zero]
  have hmN : inner ℝ m (normalVector θ) = h := by
    dsimp [m]
    rw [midpoint_eq_smul_add, real_inner_smul_left, inner_add_left, hxsN, hxtN]
    norm_num
    ring
  have hyhalf (u : Set.Icc (0 : ℝ) 2) :
      inner ℝ (y u - m) (normalVector θ) ≤ 0 := by
    unfold y cyclicComplement Function.concatUnitIntervals
    split_ifs
    · rw [inner_sub_left, hmN]
      have hh := hhalf (Set.Icc.convexComb t ⟨b, hab.le, le_rfl⟩
        (Set.projIcc 0 1 (by norm_num) (u : ℝ)))
      simp only [normalHalfPlane, Bool.false_eq_true, ↓reduceIte, Set.mem_ofPred_eq] at hh
      simpa only [Function.comp_apply] using sub_nonpos.mpr hh
    · rw [inner_sub_left, hmN]
      have hh := hhalf (Set.Icc.convexComb ⟨a, le_rfl, hab.le⟩ s
        (Set.projIcc 0 1 (by norm_num) ((u : ℝ) - 1)))
      simp only [normalHalfPlane, Bool.false_eq_true, ↓reduceIte, Set.mem_ofPred_eq] at hh
      simpa only [Function.comp_apply] using sub_nonpos.mpr hh
  have hymLift : IsCurveAngleLift y m (fun u ↦
      θ.toReal + Complex.arg (-frameComplex θ (y u - m)) + Real.pi) :=
    isCurveAngleLift_frameArg_neg_add_pi_of_inner_nonpos θ hy hyhalf hym
  let ε := min (r / 2) (d / 4)
  have hε : 0 < ε := lt_min (half_pos hr) (by positivity)
  have hεr : ε < r := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hr)
  let q := m - ε • normalVector θ
  have hnormN : ‖normalVector θ‖ = 1 := by
    rw [← θ.coe_toReal]
    exact norm_normalVector_real θ.toReal
  have hqm : dist q m = ε := by
    rw [dist_eq_norm]
    simp only [q, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, hnormN,
      mul_one, abs_of_pos hε]
  have hqclose : dist q m < r := hqm.trans_lt hεr
  have hyqLift := hymLift.add_principal_basepoint_correction hy (hdot q hqclose)
  let z : Set.Icc (0 : ℝ) 1 → Point := fun u ↦ x (Set.Icc.convexComb s t u)
  have hz : Continuous z := hx.comp (Set.Icc.continuous_convexComb _ _)
  have hzN (u : Set.Icc (0 : ℝ) 1) : inner ℝ (z u) (normalVector θ) = h := by
    apply inner_eq_of_mem_segment hxsN hxtN
    rw [← hsegment]
    exact ⟨Set.Icc.convexComb s t u, convexComb_between hst.le u, rfl⟩
  have hqN : inner ℝ q (normalVector θ) = h - ε := by
    dsimp [q]
    rw [inner_sub_left, real_inner_smul_left, hmN]
    have hNN : inner ℝ (normalVector θ) (normalVector θ) = 1 := by
      rw [← θ.coe_toReal]
      exact inner_normalVector_self θ.toReal
    rw [hNN, mul_one]
  have hzright (u : Set.Icc (0 : ℝ) 1) :
      0 ≤ inner ℝ (z u - q) (normalVector θ) := by
    rw [inner_sub_left, hzN, hqN]
    linarith
  have hzq (u : Set.Icc (0 : ℝ) 1) : z u ≠ q := by
    intro heq
    have := congrArg (fun w : Point ↦ inner ℝ w (normalVector θ)) heq
    rw [hzN, hqN] at this
    linarith
  have hzqLift : IsCurveAngleLift z q
      (fun u ↦ θ.toReal + Complex.arg (frameComplex θ (z u - q))) :=
    isCurveAngleLift_frameArg_of_inner_nonneg θ hz hzright hzq
  let doubleParam : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 2 := fun u ↦
    ⟨2 * (u : ℝ), by constructor <;> nlinarith [u.property.1, u.property.2]⟩
  have hdouble : Continuous doubleParam := by
    exact Continuous.subtype_mk (continuous_const.mul continuous_subtype_val) _
  let y₁ : Set.Icc (0 : ℝ) 1 → Point := y ∘ doubleParam
  have hy₁ : Continuous y₁ := hy.comp hdouble
  have hy₁qLift : IsCurveAngleLift y₁ q
      ((fun u ↦ θ.toReal + Complex.arg (-frameComplex θ (y u - m)) + Real.pi +
        Complex.arg (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm (y u - m)) *
            Complex.orthonormalBasisOneI.repr.symm (y u - q))) ∘
          doubleParam) := hyqLift.comp hdouble
  have hjoin : z ⟨1, by norm_num⟩ = y₁ ⟨0, by norm_num⟩ := by
    simp [z, y₁, doubleParam, y]
  have htm : x t - m = (d / 2) • tangentVector θ := by
    dsimp [m]
    rw [midpoint_eq_smul_add, hdirection]
    norm_num
    module
  have hsm : x s - m = -(d / 2) • tangentVector θ := by
    dsimp [m]
    rw [midpoint_eq_smul_add, hdirection]
    norm_num
    module
  have hTT : inner ℝ (tangentVector θ) (tangentVector θ) = 1 := by
    rw [← θ.coe_toReal]
    exact inner_tangentVector_self θ.toReal
  have hNN : inner ℝ (normalVector θ) (normalVector θ) = 1 := by
    rw [← θ.coe_toReal]
    exact inner_normalVector_self θ.toReal
  have hNT : inner ℝ (normalVector θ) (tangentVector θ) = 0 := by
    rw [real_inner_comm]
    exact htn
  have hframe_tm : frameComplex θ (x t - m) = (d / 2 : ℝ) * Complex.I := by
    rw [htm]
    apply Complex.ext
    · rw [frameComplex_re, real_inner_smul_left, htn]
      simp
    · rw [frameComplex_im, real_inner_smul_left, hTT]
      simp
  have hframe_sm : frameComplex θ (x s - m) = -(d / 2 : ℝ) * Complex.I := by
    rw [hsm]
    apply Complex.ext
    · rw [frameComplex_re, real_inner_smul_left, htn]
      simp
    · rw [frameComplex_im, real_inner_smul_left, hTT]
      simp
  have htq : x t - q = ε • normalVector θ + (d / 2) • tangentVector θ := by
    calc
      x t - q = (x t - m) + ε • normalVector θ := by dsimp [q]; abel
      _ = _ := by rw [htm]; abel
  have hsq : x s - q = ε • normalVector θ - (d / 2) • tangentVector θ := by
    calc
      x s - q = (x s - m) + ε • normalVector θ := by dsimp [q]; abel
      _ = _ := by rw [hsm]; module
  have hframe_tq : frameComplex θ (x t - q) = ε + (d / 2 : ℝ) * Complex.I := by
    rw [htq]
    apply Complex.ext
    · rw [frameComplex_re, inner_add_left, real_inner_smul_left,
        real_inner_smul_left, hNN, htn]
      simp
    · rw [frameComplex_im, inner_add_left, real_inner_smul_left,
        real_inner_smul_left, hNT, hTT]
      simp
  have hframe_sq : frameComplex θ (x s - q) = ε - (d / 2 : ℝ) * Complex.I := by
    rw [hsq]
    apply Complex.ext
    · rw [frameComplex_re, inner_sub_left, real_inner_smul_left,
        real_inner_smul_left, hNN, htn]
      simp
    · rw [frameComplex_im, inner_sub_left, real_inner_smul_left,
        real_inner_smul_left, hNT, hTT]
      simp
  have hcorr_t :
      Complex.arg (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm (x t - m)) *
          Complex.orthonormalBasisOneI.repr.symm (x t - q)) =
        Complex.arg (frameComplex θ (x t - q)) - Real.pi / 2 := by
    apply relative_arg_of_frame_eq_pos_I (half_pos hd) hframe_tm
    rw [hframe_tq]
    simpa using hε
  have hcorr_s :
      Complex.arg (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm (x s - m)) *
          Complex.orthonormalBasisOneI.repr.symm (x s - q)) =
        Complex.arg (frameComplex θ (x s - q)) + Real.pi / 2 := by
    apply relative_arg_of_frame_eq_neg_I (half_pos hd) hframe_sm
    rw [hframe_sq]
    simpa using hε
  have harg_tm : Complex.arg ((d / 2 : ℝ) * Complex.I) = Real.pi / 2 := by
    rw [Complex.arg_real_mul _ (half_pos hd), Complex.arg_I]
  have harg_sm : Complex.arg (-((d / 2 : ℝ) * Complex.I)) = -Real.pi / 2 := by
    rw [show -((d / 2 : ℝ) * Complex.I) = (d / 2 : ℝ) * (-Complex.I) by ring,
      Complex.arg_real_mul _ (half_pos hd), Complex.arg_neg_I]
    ring
  have hneg_frame_sm : -frameComplex θ (x s - m) = (d / 2 : ℝ) * Complex.I := by
    rw [hframe_sm]
    ring
  have hneg_frame_tm : -frameComplex θ (x t - m) = -((d / 2 : ℝ) * Complex.I) := by
    rw [hframe_tm]
  have hz0 : z ⟨0, by norm_num⟩ = x s := by simp [z]
  have hz1 : z ⟨1, by norm_num⟩ = x t := by simp [z]
  have hy₁0 : y₁ ⟨0, by norm_num⟩ = x t := by
    simp [y₁, doubleParam, y]
  have hy₁1 : y₁ ⟨1, by norm_num⟩ = x s := by
    simp [y₁, doubleParam, y]
  have hwinding : curveWinding (by norm_num)
      (Function.concatUnitIntervals z y₁) q = 1 := by
    rw [curveWinding_concatUnitIntervals hzqLift hy₁qLift hjoin,
      hzqLift.curveWinding_eq, hy₁qLift.curveWinding_eq]
    rw [hz1, hz0]
    simp only [Function.comp_apply]
    simp [doubleParam, y, cyclicComplement]
    simp at hcorr_t hcorr_s
    rw [hneg_frame_sm, hneg_frame_tm, harg_tm, harg_sm, hcorr_t, hcorr_s]
    field_simp [Real.pi_ne_zero]
    ring
  have hdouble_surj : Function.Surjective doubleParam := by
    intro u
    refine ⟨⟨(u : ℝ) / 2, by constructor <;> nlinarith [u.property.1, u.property.2]⟩, ?_⟩
    apply Subtype.ext
    dsimp [doubleParam]
    ring
  have hrange_y₁ : Set.range y₁ = Set.range y := by
    change Set.range (y ∘ doubleParam) = Set.range y
    rw [Set.range_comp, hdouble_surj.range_eq, Set.image_univ]
  have hrange_w : Set.range (Function.concatUnitIntervals z y₁) = Set.range x := by
    rw [Function.range_concatUnitIntervals z y₁ hjoin, hrange_y₁]
    change Set.range z ∪ Set.range (Function.concatUnitIntervals
      (x ∘ Set.Icc.convexComb t ⟨b, hab.le, le_rfl⟩)
      (x ∘ Set.Icc.convexComb ⟨a, le_rfl, hab.le⟩ s)) = Set.range x
    rw [Function.range_concatUnitIntervals _ _ (by simpa using hclosed.symm),
      show Set.range z = x '' Set.Icc s t by
        change Set.range (x ∘ Set.Icc.convexComb s t) = _
        exact range_comp_convexComb hst.le x,
      range_comp_convexComb t.property.2 x, range_comp_convexComb s.property.1 x]
    ext p
    constructor
    · rintro (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩) <;>
        exact Set.mem_range_self u
    · rintro ⟨u, rfl⟩
      by_cases hus : u ≤ s
      · exact Or.inr (Or.inr ⟨u, ⟨u.property.1, hus⟩, rfl⟩)
      by_cases hut : u ≤ t
      · exact Or.inl ⟨u, ⟨le_of_not_ge hus, hut⟩, rfl⟩
      · exact Or.inr (Or.inl ⟨u, ⟨le_of_not_ge hut, u.property.2⟩, rfl⟩)
  have hwinding_eq_x (p : Point) (hp : p ∉ Set.range x) :
      curveWinding (by norm_num) (Function.concatUnitIntervals z y₁) p =
        curveWinding hab.le x p := by
    obtain ⟨α, hα⟩ := exists_curveAngleLift_of_avoids hab hx hp
    let φst := Set.Icc.convexComb s t
    let φtb := Set.Icc.convexComb t ⟨b, hab.le, le_rfl⟩
    let φas := Set.Icc.convexComb ⟨a, le_rfl, hab.le⟩ s
    have hzα : IsCurveAngleLift z p (α ∘ φst) := hα.comp (Set.Icc.continuous_convexComb _ _)
    have htbα : IsCurveAngleLift (x ∘ φtb) p (α ∘ φtb) :=
      hα.comp (Set.Icc.continuous_convexComb _ _)
    have hasα : IsCurveAngleLift (x ∘ φas) p (α ∘ φas) :=
      hα.comp (Set.Icc.continuous_convexComb _ _)
    have htailJoin : (x ∘ φtb) ⟨1, by norm_num⟩ = (x ∘ φas) ⟨0, by norm_num⟩ := by
      simpa [φtb, φas] using hclosed.symm
    have hyp : p ∉ Set.range y := by
      rintro ⟨u, rfl⟩
      apply hp
      unfold y cyclicComplement Function.concatUnitIntervals
      split_ifs <;> exact ⟨_, rfl⟩
    obtain ⟨β, hβ⟩ := exists_curveAngleLift_of_avoids (by norm_num) hy hyp
    have hy₁wind : curveWinding (by norm_num) y₁ p = curveWinding (by norm_num) y p := by
      apply curveWinding_comp_of_endpoints (by norm_num) (by norm_num) ⟨β, hβ⟩ hdouble
      · apply Subtype.ext
        simp [doubleParam]
      · apply Subtype.ext
        simp [doubleParam]
    rw [curveWinding_concatUnitIntervals hzα (hβ.comp hdouble) hjoin, hy₁wind]
    change curveWinding (by norm_num) z p +
      curveWinding (by norm_num) (Function.concatUnitIntervals (x ∘ φtb) (x ∘ φas)) p = _
    rw [curveWinding_concatUnitIntervals htbα hasα htailJoin]
    rw [hzα.curveWinding_eq, htbα.curveWinding_eq, hasα.curveWinding_eq,
      hα.curveWinding_eq]
    have hst0 : α (φst ⟨0, by norm_num⟩) = α s := congrArg α (by simp [φst])
    have hst1 : α (φst ⟨1, by norm_num⟩) = α t := congrArg α (by simp [φst])
    have htb0 : α (φtb ⟨0, by norm_num⟩) = α t := congrArg α (by simp [φtb])
    have htb1 : α (φtb ⟨1, by norm_num⟩) = α ⟨b, hab.le, le_rfl⟩ :=
      congrArg α (by simp [φtb])
    have has0 : α (φas ⟨0, by norm_num⟩) = α ⟨a, le_rfl, hab.le⟩ :=
      congrArg α (by simp [φas])
    have has1 : α (φas ⟨1, by norm_num⟩) = α s := congrArg α (by simp [φas])
    simp only [Function.comp_apply]
    rw [hst0, hst1, htb0, htb1, has0, has1]
    ring
  have hqrange : q ∉ Set.range x := by
    rw [← hrange_w]
    intro hq
    obtain ⟨α, hα⟩ := exists_curveAngleLift_of_curveWinding_ne_zero
      (a := 0) (b := 2) (by norm_num)
      (by rw [hwinding]; norm_num)
    obtain ⟨u, hu⟩ := hq
    have hc := (hα.2 u).1
    have hs := (hα.2 u).2
    rw [hu, sub_self] at hc hs
    simp at hc hs
    nlinarith only [hc, hs, Real.cos_sq_add_sin_sq (α u)]
  have hwinding_q : curveWinding hab.le x q = 1 := by
    rw [← hwinding_eq_x q hqrange, hwinding]
  refine ⟨hab, hΓ, hx, rfl, hclosed, hinj, ?_⟩
  intro p hp
  obtain ⟨U, V, hUopen, hVopen, hUconn, hVconn, hUbounded, hVunbounded, hdis,
    hcover, hfrontU, hfrontV, hcompU, hcompV⟩ := jordan_separation hΓ
  have hqcompl : q ∈ (Set.range x)ᶜ := hqrange
  have hqUV : q ∈ U ∪ V := hcover.symm.subset hqcompl
  have hqU : q ∈ U := by
    rcases hqUV with hqU | hqV
    · exact hqU
    · exfalso
      let _ : PreconnectedSpace V := Subtype.preconnectedSpace hVconn.isPreconnected
      have hlc : IsLocallyConstant
          (fun z : V ↦ curveWinding hab.le x z.val) := by
        apply (IsLocallyConstant.iff_exists_open _).mpr
        intro z
        have hzout : z.val ∉ Set.range x := by
          have hzcompl : z.val ∈ (Set.range x)ᶜ := hcover ▸ Or.inr z.property
          exact hzcompl
        obtain ⟨W, hWopen, hzW, hWeq⟩ :=
          curveWinding_locally_constant_off_range hab.le hx hclosed hzout
        exact ⟨Subtype.val ⁻¹' W, hWopen.preimage continuous_subtype_val, hzW,
          fun z' hz' ↦ hWeq z'.val hz'⟩
      have hrangeBounded : Bornology.IsBounded (Set.range x) :=
        by simpa only [Set.image_univ] using (isCompact_univ.image hx).isBounded
      obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Point)).mp
        hrangeBounded
      have hRnonneg : 0 ≤ R := by
        have := hR (Set.mem_range_self ⟨a, le_rfl, hab.le⟩)
        have hnorm : ‖x ⟨a, le_rfl, hab.le⟩‖ ≤ R := by
          simpa [Metric.mem_closedBall, dist_zero_right] using this
        exact (norm_nonneg _).trans hnorm
      have hvfar : ∃ v ∈ V, R + 1 < ‖v‖ := by
        by_contra hn
        push Not at hn
        apply hVunbounded
        refine (Metric.isBounded_iff_subset_closedBall (0 : Point)).2 ⟨R + 1, ?_⟩
        intro v hv
        simpa [Metric.mem_closedBall, dist_zero_right] using hn v hv
      obtain ⟨v, hvV, hvnorm⟩ := hvfar
      have hvzero : curveWinding hab.le x v = 0 := by
        apply curveWinding_eq_zero_of_inner_pos hab.le hx hclosed v (-v)
        · exact neg_ne_zero.mpr (by
            intro hv0
            rw [hv0, norm_zero] at hvnorm
            linarith)
        · intro u
          rw [inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq]
          rw [← real_inner_comm v (x u)]
          have hxu := hR (Set.mem_range_self u)
          have hinner := abs_real_inner_le_norm (x u) v
          have hxnorm : ‖x u‖ ≤ R := by
            simpa [Metric.mem_closedBall, dist_zero_right] using hxu
          have hvpos : 0 < ‖v‖ := lt_of_le_of_lt hRnonneg (lt_add_one R) |>.trans hvnorm
          have hvlarge : R < ‖v‖ := lt_trans (lt_add_one R) hvnorm
          have hlower : inner ℝ (x u) v ≤ ‖x u‖ * ‖v‖ := le_trans (le_abs_self _) hinner
          have hprod : ‖x u‖ * ‖v‖ < ‖v‖ * ‖v‖ :=
            lt_of_le_of_lt (mul_le_mul_of_nonneg_right hxnorm (norm_nonneg v))
              (mul_lt_mul_of_pos_right hvlarge hvpos)
          rw [pow_two]
          linarith
      have heq := hlc.apply_eq_of_preconnectedSpace ⟨q, hqV⟩ ⟨v, hvV⟩
      rw [hwinding_q, hvzero] at heq
      norm_num at heq
  have hqInterior : q ∈ jordanInterior (Set.range x) := by
    refine ⟨hqrange, ?_⟩
    rw [hcompU q hqU]
    exact hUbounded
  have hpUV : p ∈ U ∪ V := hcover.symm.subset hp.1
  have hpU : p ∈ U := by
    rcases hpUV with hpU | hpV
    · exact hpU
    · exfalso
      apply hVunbounded
      rw [← hcompV p hpV]
      exact hp.2
  let _ : PreconnectedSpace U := Subtype.preconnectedSpace hUconn.isPreconnected
  have hlcU : IsLocallyConstant (fun z : U ↦ curveWinding hab.le x z.val) := by
    apply (IsLocallyConstant.iff_exists_open _).mpr
    intro z
    have hzout : z.val ∉ Set.range x := by
      have : z.val ∈ (Set.range x)ᶜ := hcover ▸ Or.inl z.property
      exact this
    obtain ⟨W, hWopen, hzW, hWeq⟩ :=
      curveWinding_locally_constant_off_range hab.le hx hclosed hzout
    exact ⟨Subtype.val ⁻¹' W, hWopen.preimage continuous_subtype_val, hzW,
      fun z' hz' ↦ hWeq z'.val hz'⟩
  exact (hlcU.apply_eq_of_preconnectedSpace ⟨p, hpU⟩ ⟨q, hqU⟩).trans hwinding_q

end MovingSofa
