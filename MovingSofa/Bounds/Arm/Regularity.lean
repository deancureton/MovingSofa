import MovingSofa.Analysis.SurfaceMeasure.Boundary
import MovingSofa.Cap.DensityExistence

/-!
# Regularity of the arm length function of a balanced maximum cap

For a balanced maximum cap `K` of rotation angle `π / 2` the arm length function `f_K` is
absolutely continuous on `[0, π / 2]` and satisfies `f_K' ≥ m₀ ∘ g_K` almost everywhere on
`(0, π / 2)`.

The argument combines three inputs. The differentiation identity
`positiveArm_stieltjes_surface` for the positive arm length, read on an interval `(0, t]` with
`t < π / 2`, expresses `f_K(t) - f_K(0)` as the integral of `g_K` minus the surface measure of the
arc traversed. The surface measure on that arc has a real density bounded by `k₀ ∘ g_K`, by
`exists_capDensity_right_le_magicDensity`. Together they present `f_K` on `[0, π / 2)` as the
primitive of `w = g_K - ρ`; continuity of `f_K` on the closed interval
(`nondegenerateCap_continuity`) upgrades the representation to `[0, π / 2]`, whence absolute
continuity and `f_K' = w ≥ g_K - k₀ ∘ g_K = m₀ ∘ g_K` almost everywhere.

The module also records the pointwise data accompanying that differential inequality: both arm
length functions of a nondegenerate cap are nonnegative, and the right one has initial value
`f_K(0) = 1`.
-/

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- A function on the interval subtype `Set.Icc a b`, extended to `ℝ` by zero. -/
def extendIntervalScalar {a b : ℝ} (f : Set.Icc a b → ℝ) (t : ℝ) : ℝ := by
  classical
  exact if h : t ∈ Set.Icc a b then f ⟨t, h⟩ else 0

/-- Inside its interval the zero extension agrees with the original subtype function. -/
theorem extendIntervalScalar_of_mem {a b : ℝ} (f : Set.Icc a b → ℝ) {t : ℝ}
    (ht : t ∈ Set.Icc a b) : extendIntervalScalar f t = f ⟨t, ht⟩ := by
  classical
  simp only [extendIntervalScalar, dite_eq_left ht]

/-- The right arm length of a nondegenerate right-angle cap at the horizontal normal equals one.
Lowering the contact there onto the base line stays inside the cap and meets the same supporting
line, so the infimum of the tangent heights of that edge is at most zero; the contacts coincide,
so the contact itself has height zero, and the outer corner at that angle has height
`h_K(π / 2) = 1`. -/
theorem tangentArmLengths_right_zero_eq_one (K : RightAngleCapSpace)
    (hD : ∃ r s, HasCapDensities K r s) : (tangentArmLengths K 0).1.1 = 1 := by
  have hAmem : (edgeVertices K.val ((0 : ℝ) : Real.Angle)).1 ∈
      exposedEdge K.val ((0 : ℝ) : Real.Angle) := edgeVertices_fst_mem _ _
  set A : Point := (edgeVertices K.val ((0 : ℝ) : Real.Angle)).1 with hAdef
  set B : Point := A - A 1 • normalVector ((Real.pi / 2 : ℝ) : Real.Angle) with hBdef
  -- the lowered contact lies on the same supporting line and on the base line
  have hBline : B ∈ exposedEdge K.val ((0 : ℝ) : Real.Angle) := by
    refine ⟨K.base_projection_mem hAmem.1, ?_⟩
    change inner ℝ B (normalVector ((0 : ℝ) : Real.Angle)) = supportValue K.val _
    rw [hBdef, inner_sub_left, real_inner_smul_left, inner_normalVector_normalVector]
    simp only [sub_zero, Real.cos_pi_div_two, mul_zero, sub_zero]
    exact hAmem.2
  have hBtan : inner ℝ B (tangentVector ((0 : ℝ) : Real.Angle)) = 0 := by
    rw [hBdef, inner_sub_left, real_inner_smul_left, inner_tangentVector_zero,
      ← normalVector_add_pi_div_two_real 0, inner_normalVector_normalVector]
    norm_num
  -- the two contacts coincide, so the edge is a single point of height zero
  have hcontact := (capDensities_contact_eq K hD).1 0 ⟨le_rfl, by positivity⟩
  have hAeq : A = (edgeVertices K.val ((0 : ℝ) : Real.Angle)).2 := hcontact.1
  have hA1le : A 1 ≤ 0 := by
    have h1 : A 1 = sInf ((fun p ↦ inner ℝ p (tangentVector ((0 : ℝ) : Real.Angle))) ''
        exposedEdge K.val ((0 : ℝ) : Real.Angle)) := by
      rw [← inner_tangentVector_zero A, hAeq, inner_edgeVertices_snd_tangent]
    rw [h1]
    refine csInf_le ?_ ⟨B, hBline, hBtan⟩
    exact ((isCompact_exposedEdge K.val _).image
      (continuous_id.inner continuous_const)).bddBelow
  have hA1ge : 0 ≤ A 1 := by
    simpa only [inner_normalVector_pi_div_two] using
      K.inner_normalVector_pi_div_two_nonneg hAmem.1
  have hA1 : A 1 = 0 := le_antisymm hA1le hA1ge
  -- the outer corner at the horizontal normal has unit height
  have hy : inner ℝ
      (rotatingHallwayParts (K.val : Set Point) ((0 : ℝ) : Real.Angle)).outerCorner
      (tangentVector ((0 : ℝ) : Real.Angle)) = 1 := by
    change inner ℝ (supportingPlacement (K.val : Set Point) ((0 : ℝ) : Real.Angle)
      hallwayParts.outerCorner) _ = 1
    rw [inner_supportingPlacement_tangentVector, Real.Angle.coe_zero, zero_add,
      K.property.2.2.2.1]
    simp [hallwayParts]
  simp only [tangentArmLengths, capVertices, inner_sub_left, hy, ← hAdef,
    inner_tangentVector_zero, hA1, sub_zero]

/-- Both arm length functions of a nondegenerate right-angle cap are nonnegative. -/
theorem nondegenerateCapData_arm_nonneg (K : RightAngleCapSpace)
    (hD : ∃ r s, HasCapDensities K r s) (t : Set.Icc (0 : ℝ) (Real.pi / 2)) :
    0 ≤ (nondegenerateCapData K hD).2.1 t ∧ 0 ≤ (nondegenerateCapData K hD).2.2 t := by
  refine ⟨?_, tangentArm_fst_nonneg K t.property⟩
  simp only [nondegenerateCapData]
  split_ifs
  · exact (tangentArmLengths_right_nonneg K t).2
  · exact (tangentArmLengths_right_nonneg K t).1

/-- Absolute continuity and the almost everywhere derivative of a function `G` that agrees on
`[a, b]` with a function `F` which is a primitive of `w` on the half-open interval `[a, b)`. Only
continuity of `F` at `b` is needed there, so no limit of the primitive has to be computed. -/
private theorem absolutelyContinuousOnInterval_and_ae_hasDerivAt_of_eqOn_Ico
    {a b : ℝ} (hab : a < b) {F G w : ℝ → ℝ} (hF : ContinuousOn F (Set.Icc a b))
    (hw : IntervalIntegrable w volume a b)
    (hFw : ∀ t ∈ Set.Ico a b, F t = F a + ∫ y in a..t, w y)
    (hGF : Set.EqOn G F (Set.Icc a b)) :
    AbsolutelyContinuousOnInterval G a b ∧
      ∀ᵐ t ∂volume.restrict (Set.Ioo a b), HasDerivAt G (w t) t := by
  set Φ : ℝ → ℝ := fun x ↦ F a + ∫ y in a..x, w y
  have hΦAC : AbsolutelyContinuousOnInterval Φ a b :=
    ((LipschitzWith.const (F a)).lipschitzOnWith.absolutelyContinuousOnInterval).add
      (hw.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp [hab.le]))
  have hΦcont : ContinuousOn Φ (Set.Icc a b) := by
    simpa only [Set.uIcc_of_le hab.le] using hΦAC.continuousOn
  have heq : Set.EqOn G Φ (Set.Icc a b) := by
    refine hGF.trans (Set.EqOn.of_subset_closure (fun x hx ↦ hFw x hx) hF hΦcont
      Set.Ico_subset_Icc_self ?_)
    rw [closure_Ico hab.ne]
  refine ⟨hΦAC.congr fun x hx ↦
    (heq (by simpa only [Set.uIcc_of_le hab.le] using hx)).symm, ?_⟩
  refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
  filter_upwards [hw.ae_hasDerivAt_integral] with x hx hxo
  have hxu : x ∈ Set.uIcc a b := by
    simpa only [Set.uIcc_of_le hab.le] using ⟨hxo.1.le, hxo.2.le⟩
  refine ((hx hxu a (by simp [hab.le])).const_add (F a)).congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds hxo] with y hyo
  exact heq ⟨hyo.1.le, hyo.2.le⟩

/-- The differentiation identity for the positive arm length, restricted to an interval `(0, t]`
with `t < π / 2`: the positive arm length increases by the integral of the positive tangent arm
length minus the surface measure of the arc of normal directions traversed. Restricting to
`t < π / 2` keeps the possibly nonzero top-face atom of the surface measure out of the
identity. -/
private theorem positiveArm_sub_eq_integral_sub_surface (K : RightAngleCapSpace) {t : ℝ}
    (ht : t ∈ Set.Ico (0 : ℝ) (Real.pi / 2)) :
    (tangentArmLengths K t).1.1 - (tangentArmLengths K 0).1.1 =
      (∫ u in Set.Ioc (0 : ℝ) t, (tangentArmLengths K u).2.1) -
        (surfaceAreaMeasure K.val
          ((fun u : ℝ ↦ (u : Real.Angle)) '' Set.Ioc (0 : ℝ) t)).toReal := by
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hmem0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨le_rfl, hle⟩
  have htmem : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨ht.1, ht.2.le⟩
  obtain ⟨F, hF, hinc⟩ := positiveArm_stieltjes_surface K
  have hzx : (⟨0, hmem0⟩ : Set.Icc (0 : ℝ) (Real.pi / 2)) ≤ ⟨t, htmem⟩ :=
    Subtype.mk_le_mk.mpr ht.1
  have himg : (fun u : Set.Icc (0 : ℝ) (Real.pi / 2) ↦ (u : ℝ)) ''
      Set.Ioc (⟨0, hmem0⟩ : Set.Icc (0 : ℝ) (Real.pi / 2)) ⟨t, htmem⟩ =
      Set.Ioc (0 : ℝ) t := by
    apply Set.eq_of_subset_of_subset
    · rintro y ⟨u, hu, rfl⟩
      exact ⟨hu.1, hu.2⟩
    · intro y hy
      exact ⟨⟨y, ⟨hy.1.le, hy.2.trans ht.2.le⟩⟩, ⟨hy.1, hy.2⟩, rfl⟩
  have himg2 : (fun u : Set.Icc (0 : ℝ) (Real.pi / 2) ↦ ((u : ℝ) : Real.Angle)) ''
      Set.Ioc (⟨0, hmem0⟩ : Set.Icc (0 : ℝ) (Real.pi / 2)) ⟨t, htmem⟩ =
      (fun y : ℝ ↦ (y : Real.Angle)) '' Set.Ioc (0 : ℝ) t := by
    rw [← himg, Set.image_image]
  have hEpos : ∀ y ∈ Set.Ioc (⟨0, hmem0⟩ : Set.Icc (0 : ℝ) (Real.pi / 2)) ⟨t, htmem⟩,
      0 < (y : ℝ) := fun y hy ↦ hy.1
  have h := hinc _ measurableSet_Ioc hEpos
  rw [intervalStieltjesMeasure_Ioc F _ _ hzx, himg, himg2, hF, hF] at h
  push_cast at h ⊢
  linarith [h]

theorem balancedMaximumCap_arm_regularity (K : RightAngleCapSpace)
    (hK : IsBalancedMaximumCap K) :
    ∃ hD : ∃ r s, HasCapDensities K r s,
      AbsolutelyContinuousOnInterval
        (extendIntervalScalar (nondegenerateCapData K hD).2.1) 0 (Real.pi / 2) ∧
      ∀ᵐ t ∂volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)),
        magicFunctions.2
          (Real.toNNReal (extendIntervalScalar (nondegenerateCapData K hD).2.2 t)) ≤
        deriv (extendIntervalScalar (nondegenerateCapData K hD).2.1) t := by
  have hTpos : (0 : ℝ) < Real.pi / 2 := by positivity
  have hle : (0 : ℝ) ≤ Real.pi / 2 := hTpos.le
  obtain ⟨rd, sd, hrs, -⟩ := balancedMaximumCap_hasDensities K hK
  have hD : ∃ r s, HasCapDensities K r s := ⟨rd, sd, hrs⟩
  refine ⟨hD, ?_⟩
  obtain ⟨-, -, hFcont, hGcont, -, -, -⟩ := nondegenerateCap_continuity K hD
  -- the continuous representatives of `f_K` and `g_K`, obtained by clamping the parameter
  set fc : ℝ → ℝ :=
    fun t ↦ (nondegenerateCapData K hD).2.1 (Set.projIcc 0 (Real.pi / 2) hle t) with hfcdef
  set gc : ℝ → ℝ :=
    fun t ↦ (nondegenerateCapData K hD).2.2 (Set.projIcc 0 (Real.pi / 2) hle t) with hgcdef
  have hfccont : Continuous fc := hFcont.comp continuous_projIcc
  have hgccont : Continuous gc := hGcont.comp continuous_projIcc
  have hext_f : Set.EqOn (extendIntervalScalar (nondegenerateCapData K hD).2.1) fc
      (Set.Icc 0 (Real.pi / 2)) := by
    intro x hx
    rw [extendIntervalScalar_of_mem _ hx, hfcdef]
    simp only [Set.projIcc_of_mem hle hx]
  have hext_g : ∀ x ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      extendIntervalScalar (nondegenerateCapData K hD).2.2 x = gc x := by
    intro x hx
    rw [extendIntervalScalar_of_mem _ hx, hgcdef]
    simp only [Set.projIcc_of_mem hle hx]
  -- on `[0, π / 2)` the arm length function is the positive arm length `f⁺_K`
  have hfcval : ∀ x ∈ Set.Ico (0 : ℝ) (Real.pi / 2), fc x = (tangentArmLengths K x).1.1 := by
    intro x hx
    rw [hfcdef]
    simp only [Set.projIcc_of_mem hle (Set.Ico_subset_Icc_self hx), nondegenerateCapData,
      ite_eq_right (ne_of_lt hx.2)]
  have hgcval : ∀ x ∈ Set.Icc (0 : ℝ) (Real.pi / 2), gc x = (tangentArmLengths K x).2.1 := by
    intro x hx
    rw [hgcdef]
    simp only [Set.projIcc_of_mem hle hx]
    rfl
  have hgcnonneg : ∀ x, 0 ≤ gc x := fun x ↦ by
    rw [hgcdef]
    exact tangentArm_fst_nonneg K (Set.projIcc 0 (Real.pi / 2) hle x).property
  -- the density of the surface measure on the first arc, bounded by `k₀ ∘ g_K`
  obtain ⟨ρ, hρint, hρle, hρeq⟩ := exists_capDensity_right_le_magicDensity K hK
  set w : ℝ → ℝ := fun t ↦ gc t - ρ t
  have hwint : IntervalIntegrable w volume 0 (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hle).2
      ((hgccont.continuousOn.integrableOn_Icc).sub hρint)
  -- the integral representation of the arm length function on `[0, π / 2)`
  have hrepr : ∀ t ∈ Set.Ico (0 : ℝ) (Real.pi / 2),
      fc t = fc 0 + ∫ y in (0 : ℝ)..t, w y := by
    intro t ht
    have hIocsub : Set.Ioc (0 : ℝ) t ⊆ Set.Ico 0 (Real.pi / 2) :=
      fun y hy ↦ ⟨hy.1.le, lt_of_le_of_lt hy.2 ht.2⟩
    have hIccsub : Set.Ioc (0 : ℝ) t ⊆ Set.Icc 0 (Real.pi / 2) :=
      hIocsub.trans Set.Ico_subset_Icc_self
    have hsplit : (∫ y in Set.Ioc (0 : ℝ) t, w y) =
        (∫ u in Set.Ioc (0 : ℝ) t, gc u) - ∫ y in Set.Ioc (0 : ℝ) t, ρ y :=
      integral_sub (hgccont.continuousOn.integrableOn_Icc.mono_set hIccsub)
        (hρint.mono_set hIccsub)
    have harm : (∫ u in Set.Ioc (0 : ℝ) t, gc u) =
        ∫ u in Set.Ioc (0 : ℝ) t, (tangentArmLengths K u).2.1 :=
      setIntegral_congr_fun measurableSet_Ioc fun u hu ↦ hgcval u (hIccsub hu)
    rw [intervalIntegral.integral_of_le ht.1, hsplit, harm,
      ← hρeq _ measurableSet_Ioc hIocsub, hfcval t ht, hfcval 0 ⟨le_rfl, hTpos⟩]
    linarith [positiveArm_sub_eq_integral_sub_surface K ht]
  -- absolute continuity on `[0, π / 2]` and the almost everywhere derivative on `(0, π / 2)`
  obtain ⟨hAC, hderiv⟩ := absolutelyContinuousOnInterval_and_ae_hasDerivAt_of_eqOn_Ico
    hTpos hfccont.continuousOn hwint hrepr hext_f
  refine ⟨hAC, ?_⟩
  have hρIoo : ∀ᵐ t ∂volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)),
      0 ≤ ρ t ∧ ρ t ≤ magicDensity (tangentArmLengths K t).2.1 :=
    ae_restrict_of_ae_restrict_of_subset Set.Ioo_subset_Icc_self hρle
  filter_upwards [hderiv, hρIoo, ae_restrict_mem measurableSet_Ioo] with t h1 h2 h3
  have h3' : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := Set.Ioo_subset_Icc_self h3
  rw [h1.deriv, hext_g t h3']
  have hval : magicFunctions.2 (Real.toNNReal (gc t)) = gc t - magicDensity (gc t) := by
    simp only [magicDensity, magicFunctions, Real.coe_toNNReal _ (hgcnonneg t)]
  have hw : w t = gc t - ρ t := rfl
  rw [hval, hw, hgcval t h3']
  linarith [h2.2]

end MovingSofa
