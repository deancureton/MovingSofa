import MovingSofa.Canonical.GerverDefinitions
import MovingSofa.Geometry.Hallway

/-!
# The paper's Gerver path and the vendor coordinate transport

`paperGerverPath` is the certified direct five-phase Gerver path read through the vendor
coordinate identification `GerverSofa.PartF.Coordinates.toPlane`.  This file records the
transport lemmas for that identification (derivatives, smoothness, continuity) and the
frame readers that express the moving frame `normalVector`/`tangentVector` in the same
coordinates.

The frame readers live here rather than in `MovingSofa/Geometry/Basic.lean` because their
statements mention `toPlane`, which `Geometry/Basic.lean` does not import; this is the
lowest module that sees both the vendor coordinates and `MovingSofa.frame`.
-/

noncomputable section

open scoped ContDiff

namespace MovingSofa

/-- The certified direct five-phase Gerver path, taking the earlier branch at each switch. -/
def paperGerverPath (t : ℝ) : Point :=
  GerverSofa.PartF.Coordinates.toPlane (GerverSofa.Romik.path GerverSofa.PartB.params t)

theorem canonical_path_rotation_eq_paper (t : ℝ) (ht : t ∈ Set.Icc 0 (Real.pi / 2)) :
    rotationMap (t : Real.Angle) (GerversSofa.p t) = paperGerverPath t :=
  GerverSofa.PartF.ProjectAdapter.integral_rotation_to_full t ht

section Transport

open GerverSofa.Romik GerverSofa.PartF.Coordinates

/-! ### Transport along the coordinate identification -/

/-- The coordinate identification `toPlane` is a continuous linear map, so it transports
derivatives of plane-valued curves. -/
theorem hasDerivAt_toPlane {q : ℝ → GerverSofa.Point} {q' : GerverSofa.Point} {t : ℝ}
    (hq : HasDerivAt q q' t) : HasDerivAt (fun s => toPlane (q s)) (toPlane q') t := by
  obtain ⟨L, hL⟩ : ∃ L : GerverSofa.Point →L[ℝ] Point, ⇑L = toPlane :=
    ⟨{ toLinearMap := linearEquiv.toLinearMap, cont := continuous_toPlane }, rfl⟩
  rw [← hL]
  simpa [Function.comp_def] using L.hasFDerivAt.comp_hasDerivAt t hq

/-- The coordinate identification `toPlane` preserves smoothness of plane-valued curves. -/
theorem contDiff_toPlane {q : ℝ → GerverSofa.Point} (hq : ContDiff ℝ ∞ q) :
    ContDiff ℝ ∞ fun t => toPlane (q t) := by
  rw [contDiff_euclidean]
  intro i
  fin_cases i
  · exact hq.fst
  · exact hq.snd

/-! ### Frame readers -/

/-- The angular frame normal is the coordinate image of the standard trigonometric pair. -/
theorem normalVector_coe_eq_toPlane (t : ℝ) :
    normalVector (t : Real.Angle) = toPlane (Real.cos t, Real.sin t) := rfl

/-- The angular frame tangent is the coordinate image of the rotated trigonometric pair. -/
theorem tangentVector_coe_eq_toPlane (t : ℝ) :
    tangentVector (t : Real.Angle) = toPlane (-Real.sin t, Real.cos t) := rfl

/-- The normal component of a body-frame vector rotated by `t` is its first coordinate. -/
theorem inner_toPlane_rot_normalVector (t : ℝ) (z : GerverSofa.Point) :
    inner ℝ (toPlane (rot t z)) (normalVector (t : Real.Angle)) = z.1 := by
  have h := Real.sin_sq_add_cos_sq t
  simp only [normalVector, MovingSofa.frame, PiLp.inner_apply, RCLike.inner_apply,
    Fin.sum_univ_two, rot, toPlane_zero_coord, toPlane_one_coord, conj_trivial,
    Matrix.cons_val_zero, Matrix.cons_val_one, Real.Angle.cos_coe, Real.Angle.sin_coe]
  linear_combination z.1 * h

/-- The tangential component of a body-frame vector rotated by `t` is its second
coordinate. -/
theorem inner_toPlane_rot_tangentVector (t : ℝ) (z : GerverSofa.Point) :
    inner ℝ (toPlane (rot t z)) (tangentVector (t : Real.Angle)) = z.2 := by
  have h := Real.sin_sq_add_cos_sq t
  simp only [tangentVector, MovingSofa.frame, PiLp.inner_apply, RCLike.inner_apply,
    Fin.sum_univ_two, rot, toPlane_zero_coord, toPlane_one_coord, conj_trivial,
    Matrix.cons_val_zero, Matrix.cons_val_one, Real.Angle.cos_coe, Real.Angle.sin_coe]
  linear_combination z.2 * h

/-- The normal frame component of a plane point is the vendor scalar product of its
coordinate pair with the vendor normal `u`. -/
theorem inner_normalVector_eq_dot (q : Point) (s : ℝ) :
    inner ℝ q (normalVector (s : Real.Angle)) =
      GerverSofa.dot (fromPlane q) (GerverSofa.u s) := by
  simp only [normalVector, MovingSofa.frame, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Real.Angle.cos_coe,
    Real.Angle.sin_coe, GerverSofa.dot, GerverSofa.u, fromPlane]
  ring

/-- The tangent frame component of a plane point is the vendor scalar product of its
coordinate pair with the vendor tangent `v`. -/
theorem inner_tangentVector_eq_dot (q : Point) (s : ℝ) :
    inner ℝ q (tangentVector (s : Real.Angle)) =
      GerverSofa.dot (fromPlane q) (GerverSofa.v s) := by
  simp only [tangentVector, MovingSofa.frame, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Real.Angle.cos_coe,
    Real.Angle.sin_coe, GerverSofa.dot, GerverSofa.v, fromPlane]
  ring

/-- The angular frame normal is a smooth function of the angle. -/
theorem contDiff_normalVector : ContDiff ℝ ∞ fun t : ℝ => normalVector (t : Real.Angle) := by
  simp only [normalVector_coe_eq_toPlane]
  exact contDiff_toPlane (Real.contDiff_cos.prodMk Real.contDiff_sin)

/-- The angular frame tangent is a smooth function of the angle. -/
theorem contDiff_tangentVector :
    ContDiff ℝ ∞ fun t : ℝ => tangentVector (t : Real.Angle) := by
  simp only [tangentVector_coe_eq_toPlane]
  exact contDiff_toPlane (Real.contDiff_sin.neg.prodMk Real.contDiff_cos)

/-! ### The paper path as a transported direct path

The hypothesis `ContDiff ℝ 1 (path GerverSofa.PartB.params)` in the lemmas below is the
first conjunct of `MovingSofa.gerver_direct_path_regularity`, which lives in a later
module; passing it as a hypothesis keeps this file free of that dependency. -/

/-- The paper path is the coordinate image of the certified direct path. -/
theorem paperGerverPath_eq_toPlane :
    paperGerverPath = fun t => toPlane (path GerverSofa.PartB.params t) := rfl

/-- The paper path differentiates by transporting the derivative of the direct path. -/
theorem hasDerivAt_paperGerverPath (hC1 : ContDiff ℝ 1 (path GerverSofa.PartB.params))
    (t : ℝ) :
    HasDerivAt paperGerverPath (toPlane (deriv (path GerverSofa.PartB.params) t)) t :=
  hasDerivAt_toPlane ((hC1.differentiable one_ne_zero t).hasDerivAt)

/-- The derivative of the paper path is the transported derivative of the direct path. -/
theorem deriv_paperGerverPath (hC1 : ContDiff ℝ 1 (path GerverSofa.PartB.params)) (t : ℝ) :
    deriv paperGerverPath t = toPlane (deriv (path GerverSofa.PartB.params) t) :=
  (hasDerivAt_paperGerverPath hC1 t).deriv

/-- The paper path is continuous. -/
theorem continuous_paperGerverPath (hC1 : ContDiff ℝ 1 (path GerverSofa.PartB.params)) :
    Continuous paperGerverPath := by
  rw [paperGerverPath_eq_toPlane]
  exact continuous_toPlane.comp hC1.continuous

/-- The paper path is continuously differentiable. -/
theorem continuous_deriv_paperGerverPath
    (hC1 : ContDiff ℝ 1 (path GerverSofa.PartB.params)) :
    Continuous (deriv paperGerverPath) := by
  rw [funext (deriv_paperGerverPath hC1)]
  exact continuous_toPlane.comp (hC1.continuous_deriv le_rfl)

end Transport

end MovingSofa
