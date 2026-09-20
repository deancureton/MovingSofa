import MovingSofa.Analysis.SurfaceMeasure.ExteriorNormal
import MovingSofa.Analysis.SurfaceMeasure.GraphDefinitions
import MovingSofa.Analysis.SurfaceMeasure.Regularity
import MovingSofa.ForMathlib.Analysis.Convex.Deriv
import MovingSofa.ForMathlib.MeasureTheory.Hausdorff.PlanarGraph
import MovingSofa.ForMathlib.Geometry.Euclidean.Segment
import MovingSofa.Geometry.Reflection
import MovingSofa.Geometry.Support
import Mathlib.Analysis.Convex.Continuous

noncomputable section

open MeasureTheory
open scoped Pointwise

namespace MovingSofa

private def negCoordinates (e : Point ≃ₗᵢ[ℝ] Point) : Point ≃ₗᵢ[ℝ] Point :=
  e.trans (LinearIsometryEquiv.neg ℝ)

private def swapCoordinates (e : Point ≃ₗᵢ[ℝ] Point) : Point ≃ₗᵢ[ℝ] Point :=
  e.trans coordinateSwap

@[simp] private theorem negCoordinates_apply (e : Point ≃ₗᵢ[ℝ] Point) (p : Point) (i : Fin 2) :
    negCoordinates e p i = -e p i := by
  simp [negCoordinates]

@[simp] private theorem swapCoordinates_apply_zero (e : Point ≃ₗᵢ[ℝ] Point)
    (p : Point) : swapCoordinates e p 0 = e p 1 := by
  simp [swapCoordinates, coordinateSwap]

@[simp] private theorem swapCoordinates_apply_one (e : Point ≃ₗᵢ[ℝ] Point)
    (p : Point) : swapCoordinates e p 1 = e p 0 := by
  simp [swapCoordinates, coordinateSwap]

/-- The upper graph height is the greatest vertical coordinate in its fiber. -/
theorem upperGraphHeight_isGreatest (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) {x : ℝ} (hx : x ∈ horizontalProjection K o e) :
    IsGreatest {y : ℝ | o + e.symm !₂[x, y] ∈ (K : Set Point)}
      (upperGraphHeight K o e x) := by
  let F : Set ℝ := {y | o + e.symm !₂[x, y] ∈ (K : Set Point)}
  let Y : Set ℝ := (fun p : Point ↦ e (p - o) 1) '' (K : Set Point)
  have hY : IsCompact Y := K.isCompact.image (by fun_prop)
  have hFc : IsClosed F := K.isClosed.preimage (by fun_prop)
  have hFY : F ⊆ Y := by
    intro y hy
    refine ⟨o + e.symm !₂[x, y], hy, ?_⟩
    simp
  have hF : IsCompact F := hY.of_isClosed_subset hFc hFY
  have hFne : F.Nonempty := by
    obtain ⟨p, hp, hpx⟩ := hx
    refine ⟨e (p - o) 1, ?_⟩
    dsimp [F]
    convert hp using 1
    apply sub_eq_zero.mp
    apply e.injective
    ext i
    fin_cases i
    · simp only [map_sub, PiLp.sub_apply] at hpx
      simp
      linarith
    · simp
  change IsGreatest F (sSup F)
  exact hF.isGreatest_sSup hFne

/-- An attained upper graph point belongs to the convex body. -/
theorem upperGraphHeight_mem (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) {x : ℝ} (hx : x ∈ horizontalProjection K o e) :
    o + e.symm !₂[x, upperGraphHeight K o e x] ∈ (K : Set Point) :=
  (upperGraphHeight_isGreatest K o e hx).1

private theorem upperGraphHeight_eq_coordinate_of_isExteriorNormal_of_pos
    (K : ConvexBody Point) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) {p : Point} (hp : p ∈ K)
    {a : Real.Angle} (ha : IsExteriorNormal K p a) (hpos : 0 < e (normalVector a) 1) :
    upperGraphHeight K o e (e (p - o) 0) = e (p - o) 1 := by
  have hx : e (p - o) 0 ∈ horizontalProjection K o e := ⟨p, hp, rfl⟩
  apply le_antisymm
  · apply le_of_not_gt
    intro hgt
    have hmem := upperGraphHeight_mem K o e hx
    have hs := ha (o + e.symm !₂[e (p - o) 0,
      upperGraphHeight K o e (e (p - o) 0)]) hmem
    rw [← e.inner_map_map] at hs
    simp only [map_sub, map_add, LinearIsometryEquiv.apply_symm_apply, PiLp.inner_apply,
      RCLike.inner_apply, conj_trivial, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, PiLp.sub_apply, PiLp.add_apply] at hs
    have hzero : e (p - o) 0 = e p 0 - e o 0 := by simp
    have hone : e (p - o) 1 = e p 1 - e o 1 := by simp
    ring_nf at hs
    rw [hzero, hone] at hgt
    rw [show -(e o 0) + e p 0 = e p 0 - e o 0 by ring] at hs
    have hnonpos : e (normalVector a) 1 *
        (upperGraphHeight K o e (e p 0 - e o 0) - (e p 1 - e o 1)) ≤ 0 := by
      nlinarith [hs]
    exact (not_lt_of_ge hnonpos) (mul_pos hpos (sub_pos.mpr hgt))
  · exact (upperGraphHeight_isGreatest K o e hx).2 (by
      show o + e.symm !₂[e (p - o) 0, e (p - o) 1] ∈ (K : Set Point)
      rw [show o + e.symm !₂[e (p - o) 0, e (p - o) 1] = p by
        apply e.injective
        ext i
        fin_cases i <;> simp [map_sub]]
      exact hp)

/-- A boundary point whose exterior normal has positive vertical coordinate lies
on the upper coordinate graph. -/
theorem eq_upperCoordinateGraph_of_isExteriorNormal_of_pos
    (K : ConvexBody Point) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) {p : Point} (hp : p ∈ K)
    {a : Real.Angle} (ha : IsExteriorNormal K p a) (hpos : 0 < e (normalVector a) 1) :
    p = o + e.symm !₂[e (p - o) 0, upperGraphHeight K o e (e (p - o) 0)] := by
  rw [upperGraphHeight_eq_coordinate_of_isExteriorNormal_of_pos K o e hp ha hpos]
  apply e.injective
  ext i
  fin_cases i <;> simp [map_sub]

private theorem eq_upperCoordinateGraph_of_maximal_verticalCoordinate
    (K : ConvexBody Point) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) {p : Point} (hp : p ∈ K)
    (hmax : ∀ q ∈ K, e (q - o) 1 ≤ e (p - o) 1) :
    p = o + e.symm !₂[e (p - o) 0, upperGraphHeight K o e (e (p - o) 0)] := by
  have hx : e (p - o) 0 ∈ horizontalProjection K o e := ⟨p, hp, rfl⟩
  have hpGreatest : IsGreatest
      {y : ℝ | o + e.symm !₂[e (p - o) 0, y] ∈ (K : Set Point)} (e (p - o) 1) := by
    constructor
    · show o + e.symm !₂[e (p - o) 0, e (p - o) 1] ∈ (K : Set Point)
      rw [show o + e.symm !₂[e (p - o) 0, e (p - o) 1] = p by
        apply e.injective
        ext i
        fin_cases i <;> simp [map_sub]]
      exact hp
    · intro y hy
      have := hmax (o + e.symm !₂[e (p - o) 0, y]) hy
      simpa using this
  have heq := (upperGraphHeight_isGreatest K o e hx).unique hpGreatest
  rw [heq]
  apply e.injective
  ext i
  fin_cases i <;> simp [map_sub]

private theorem horizontalCoordinate_le_rightBound (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) {p : Point} (hp : p ∈ K) :
    e (p - o) 0 ≤ (horizontalBounds K o e).2 := by
  exact (K.isCompact.image (by fun_prop)).isGreatest_sSup (K.nonempty.image _)
    |>.2 ⟨p, hp, rfl⟩

private theorem horizontalProjection_negCoordinates (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) :
    horizontalProjection K o (negCoordinates e) = -(horizontalProjection K o e) := by
  ext x
  simp [horizontalProjection, negCoordinates]
  constructor
  · rintro ⟨p, hp, h⟩
    exact ⟨p, hp, by linarith⟩
  · rintro ⟨p, hp, h⟩
    exact ⟨p, hp, by linarith⟩

private theorem horizontalBounds_negCoordinates (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) :
    horizontalBounds K o (negCoordinates e) =
      (-(horizontalBounds K o e).2, -(horizontalBounds K o e).1) := by
  simp only [horizontalBounds, horizontalProjection_negCoordinates, Real.sInf_neg,
    Real.sSup_neg]

private theorem leftBound_le_horizontalCoordinate (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) {p : Point} (hp : p ∈ K) :
    (horizontalBounds K o e).1 ≤ e (p - o) 0 := by
  exact (K.isCompact.image (by fun_prop)).isLeast_sInf (K.nonempty.image _)
    |>.2 ⟨p, hp, rfl⟩

private theorem eq_swapUpperGraph_of_horizontalCoordinate_eq_rightBound
    (K : ConvexBody Point) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) {p : Point} (hp : p ∈ K)
    (hpr : e (p - o) 0 = (horizontalBounds K o e).2) :
    p = o + (swapCoordinates e).symm
      !₂[swapCoordinates e (p - o) 0,
        upperGraphHeight K o (swapCoordinates e) (swapCoordinates e (p - o) 0)] := by
  apply eq_upperCoordinateGraph_of_maximal_verticalCoordinate K o (swapCoordinates e) hp
  intro q hq
  have hqle := horizontalCoordinate_le_rightBound K o e hq
  simp only [swapCoordinates_apply_one]
  simp only [map_sub, PiLp.sub_apply] at hpr hqle ⊢
  linarith

private theorem eq_negSwapUpperGraph_of_horizontalCoordinate_eq_leftBound
    (K : ConvexBody Point) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) {p : Point} (hp : p ∈ K)
    (hpl : e (p - o) 0 = (horizontalBounds K o e).1) :
    p = o + (negCoordinates (swapCoordinates e)).symm
      !₂[negCoordinates (swapCoordinates e) (p - o) 0,
        upperGraphHeight K o (negCoordinates (swapCoordinates e))
          (negCoordinates (swapCoordinates e) (p - o) 0)] := by
  apply eq_upperCoordinateGraph_of_maximal_verticalCoordinate K o
    (negCoordinates (swapCoordinates e)) hp
  intro q hq
  have hle := leftBound_le_horizontalCoordinate K o e hq
  simp only [negCoordinates_apply, swapCoordinates_apply_one]
  simp only [map_sub, PiLp.sub_apply] at hpl hle ⊢
  linarith

private def coordinateCornerSet (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) : Set Point :=
  {p | e (p - o) 0 ∈ ({(horizontalBounds K o e).1,
      (horizontalBounds K o e).2} : Set ℝ) ∧
    e (p - o) 1 ∈ ({(horizontalBounds K o (swapCoordinates e)).1,
      (horizontalBounds K o (swapCoordinates e)).2} : Set ℝ)}

private theorem coordinateCornerSet_finite (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) : (coordinateCornerSet K o e).Finite := by
  let coords : Point → ℝ × ℝ := fun p ↦ (e (p - o) 0, e (p - o) 1)
  let xs : Set ℝ := {(horizontalBounds K o e).1, (horizontalBounds K o e).2}
  let ys : Set ℝ := {(horizontalBounds K o (swapCoordinates e)).1,
    (horizontalBounds K o (swapCoordinates e)).2}
  have hcoords : Function.Injective coords := by
    intro p q hpq
    apply sub_left_injective (b := o)
    apply e.injective
    ext i
    fin_cases i
    · exact congrArg Prod.fst hpq
    · exact congrArg Prod.snd hpq
  have hfinite : (xs ×ˢ ys).Finite := Set.toFinite xs |>.prod (Set.toFinite ys)
  have hpre : (coords ⁻¹' (xs ×ˢ ys)).Finite := hfinite.preimage hcoords.injOn
  have heq : coordinateCornerSet K o e = coords ⁻¹' (xs ×ˢ ys) := by
    ext p
    simp only [coordinateCornerSet, coords, xs, ys, Set.mem_ofPred_eq, Set.mem_preimage,
      Set.mem_prod, Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [heq]
  exact hpre

private theorem hausdorffMeasure_coordinateCornerSet_eq_zero (K : ConvexBody Point)
    (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) :
    Measure.hausdorffMeasure 1 (coordinateCornerSet K o e) = 0 := by
  let _ := MeasureTheory.Measure.nullSingletonClass_hausdorff Point (by norm_num : (0 : ℝ) < 1)
  exact (coordinateCornerSet_finite K o e).measure_zero _

/-- The upper height function of a convex body is concave on its projection. -/
theorem concaveOn_upperGraphHeight (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) :
    ConcaveOn ℝ (horizontalProjection K o e) (upperGraphHeight K o e) := by
  have hproj : Convex ℝ (horizontalProjection K o e) := by
    intro x hx y hy a b ha hb hab
    obtain ⟨p, hp, hpx⟩ := hx
    obtain ⟨q, hq, hqx⟩ := hy
    refine ⟨a • p + b • q, K.convex hp hq ha hb hab, ?_⟩
    simp only [map_sub, map_add, map_smul, PiLp.sub_apply, PiLp.add_apply,
      PiLp.smul_apply] at hpx hqx ⊢
    linear_combination a * hpx + b * hqx + e o 0 * hab
  refine ⟨hproj, ?_⟩
  · intro x hx y hy a b ha hb hab
    apply (upperGraphHeight_isGreatest K o e (by
      exact hproj hx hy ha hb hab)).2
    have hpx := upperGraphHeight_mem K o e hx
    have hpy := upperGraphHeight_mem K o e hy
    have hconv := K.convex hpx hpy ha hb hab
    show o + e.symm !₂[a • x + b • y,
      a • upperGraphHeight K o e x + b • upperGraphHeight K o e y] ∈ (K : Set Point)
    rw [show o + e.symm !₂[a • x + b • y,
        a • upperGraphHeight K o e x + b • upperGraphHeight K o e y] =
        a • (o + e.symm !₂[x, upperGraphHeight K o e x]) +
          b • (o + e.symm !₂[y, upperGraphHeight K o e y]) by
      apply e.injective
      ext i
      fin_cases i <;> simp [map_add, map_smul] <;>
        linear_combination -(e o _) * hab]
    exact hconv

/-- The horizontal projection is the interval between its compact extrema. -/
theorem horizontalProjection_eq_Icc (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) :
    horizontalProjection K o e =
      Set.Icc (horizontalBounds K o e).1 (horizontalBounds K o e).2 := by
  let s := horizontalProjection K o e
  have hscompact : IsCompact s := K.isCompact.image (by fun_prop)
  have hsne : s.Nonempty := K.nonempty.image _
  have hsconv : Convex ℝ s := (concaveOn_upperGraphHeight K o e).1
  change s = Set.Icc (sInf s) (sSup s)
  apply Set.Subset.antisymm
  · exact hscompact.isBounded.subset_Icc_sInf_sSup
  · have hle := (hscompact.isLeast_sInf hsne).2 (hscompact.sSup_mem hsne)
    rw [← Set.uIcc_of_le hle, ← segment_eq_uIcc]
    exact hsconv.segment_subset (hscompact.sInf_mem hsne) (hscompact.sSup_mem hsne)

/-- The upper boundary height is locally Lipschitz inside its projection interval. -/
theorem locallyLipschitzOn_upperGraphHeight (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) :
    LocallyLipschitzOn
      (Set.Ioo (horizontalBounds K o e).1 (horizontalBounds K o e).2)
      (upperGraphHeight K o e) := by
  have hlip := (concaveOn_upperGraphHeight K o e).locallyLipschitzOn_interior
  rw [horizontalProjection_eq_Icc K o e, interior_Icc] at hlip
  exact hlip

/-- The upward normal determined by the derivative of an upper graph is exterior. -/
theorem upperGraph_deriv_isExteriorNormal (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) {x : ℝ}
    (hx : x ∈ Set.Ioo (horizontalBounds K o e).1 (horizontalBounds K o e).2)
    (hdiff : DifferentiableAt ℝ (upperGraphHeight K o e) x) :
    IsExteriorNormal K (o + e.symm !₂[x, upperGraphHeight K o e x])
      (vectorNormalAngle (e.symm !₂[-deriv (upperGraphHeight K o e) x, 1])) := by
  let g := upperGraphHeight K o e
  let q : Point := e.symm !₂[-deriv g x, 1]
  have hq : q ≠ 0 := by
    intro hzero
    have := congrFun (congrArg WithLp.ofLp (congrArg e hzero)) 1
    simp [q] at this
  change IsExteriorNormal K (o + e.symm !₂[x, g x]) (vectorNormalAngle q)
  rw [IsExteriorNormal]
  rw [normalVector_vectorNormalAngle hq]
  intro p hp
  have hxp : e (p - o) 0 ∈ horizontalProjection K o e := ⟨p, hp, rfl⟩
  have hxproj : x ∈ horizontalProjection K o e := by
    rw [horizontalProjection_eq_Icc K o e]
    exact ⟨hx.1.le, hx.2.le⟩
  have hvertical : e (p - o) 1 ≤ g (e (p - o) 0) :=
    (upperGraphHeight_isGreatest K o e hxp).2 (by
      show o + e.symm !₂[e (p - o) 0, e (p - o) 1] ∈ (K : Set Point)
      rw [show o + e.symm !₂[e (p - o) 0, e (p - o) 1] = p by
        apply e.injective
        ext i
        fin_cases i <;> simp [map_sub]]
      exact hp)
  have htangent := ConcaveOn.le_add_deriv_mul_sub
    (concaveOn_upperGraphHeight K o e) hxproj hdiff hxp
  have hvertical' : e p 1 - e o 1 ≤ g (e p 0 - e o 0) := by
    simpa only [map_sub, PiLp.sub_apply] using hvertical
  have htangent' : g (e p 0 - e o 0) ≤
      g x + deriv g x * ((e p 0 - e o 0) - x) := by
    simpa only [map_sub, PiLp.sub_apply] using htangent
  rw [inner_smul_right]
  apply mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg q))
  rw [← e.inner_map_map]
  simp only [map_sub, map_add, LinearIsometryEquiv.apply_symm_apply, q, PiLp.inner_apply,
    RCLike.inner_apply, conj_trivial, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, PiLp.sub_apply, PiLp.add_apply]
  dsimp only [g] at hvertical' htangent' ⊢
  nlinarith [hvertical', htangent']

/-- Angular normal vectors have norm one. -/
theorem norm_normalVector (a : Real.Angle) : ‖normalVector a‖ = 1 := by
  induction a using Real.Angle.induction_on with
  | _ a =>
    rw [EuclideanSpace.norm_eq]
    simp [normalVector, frame, Fin.sum_univ_two]

private theorem horizontalCoordinate_eq_endpoint_of_isExteriorNormal_of_vertical_eq_zero
    (K : ConvexBody Point) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) {p : Point} (hp : p ∈ K)
    {a : Real.Angle} (ha : IsExteriorNormal K p a)
    (hzero : e (normalVector a) 1 = 0) :
    e (p - o) 0 = (horizontalBounds K o e).1 ∨
      e (p - o) 0 = (horizontalBounds K o e).2 := by
  have hxne : e (normalVector a) 0 ≠ 0 := by
    intro hx
    have he : e (normalVector a) = 0 := by
      ext i
      fin_cases i <;> simp [hx, hzero]
    have hn : ‖e (normalVector a)‖ = 1 := by rw [e.norm_map, norm_normalVector]
    simp [he] at hn
  rcases lt_or_gt_of_ne hxne with hneg | hpos
  · left
    have hleast : IsLeast (horizontalProjection K o e) (e (p - o) 0) := by
      refine ⟨⟨p, hp, rfl⟩, ?_⟩
      rintro x ⟨q, hq, rfl⟩
      have hs := ha q hq
      rw [← e.inner_map_map] at hs
      simp only [map_sub, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
        Fin.sum_univ_two, PiLp.sub_apply, hzero] at hs
      have hxcoord : e (q - o) 0 - e (p - o) 0 = e q 0 - e p 0 := by simp
      nlinarith
    exact hleast.unique ((K.isCompact.image (by fun_prop)).isLeast_sInf (K.nonempty.image _))
  · right
    have hgreatest : IsGreatest (horizontalProjection K o e) (e (p - o) 0) := by
      refine ⟨⟨p, hp, rfl⟩, ?_⟩
      rintro x ⟨q, hq, rfl⟩
      have hs := ha q hq
      rw [← e.inner_map_map] at hs
      simp only [map_sub, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
        Fin.sum_univ_two, PiLp.sub_apply, hzero] at hs
      have hxcoord : e (q - o) 0 - e (p - o) 0 = e q 0 - e p 0 := by simp
      nlinarith
    exact hgreatest.unique ((K.isCompact.image (by fun_prop)).isGreatest_sSup
      (K.nonempty.image _))

/-- A point of a convex body admitting an exterior unit normal belongs to its frontier. -/
theorem mem_frontier_of_mem_of_isExteriorNormal (K : ConvexBody Point)
    {p : Point} (hp : p ∈ K) {a : Real.Angle} (ha : IsExteriorNormal K p a) :
    p ∈ frontier (K : Set Point) := by
  rw [mem_frontier_iff_notMem_interior hp]
  intro hpint
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior p hpint
  let q := p + (ε / 2) • normalVector a
  have hqp : q ∈ K := interior_subset (hball (by
    rw [Metric.mem_ball, dist_eq_norm]
    rw [show q - p = (ε / 2) • normalVector a by simp [q], norm_smul,
      norm_normalVector]
    rw [Real.norm_eq_abs, abs_of_pos (div_pos hε (by norm_num))]
    linarith))
  have := ha q hqp
  rw [show q - p = (ε / 2) • normalVector a by simp [q], inner_smul_left,
    real_inner_self_eq_norm_sq, norm_normalVector a] at this
  have hnonpos : ε / 2 ≤ 0 := by simpa using this
  linarith

private theorem upperGraph_tangent_orthogonal_of_isExteriorNormal
    (K : ConvexBody Point) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) {x : ℝ}
    (hx : x ∈ Set.Ioo (horizontalBounds K o e).1 (horizontalBounds K o e).2)
    (hdiff : DifferentiableAt ℝ (upperGraphHeight K o e) x) {a : Real.Angle}
    (ha : IsExteriorNormal K
      (o + e.symm !₂[x, upperGraphHeight K o e x]) a) :
    inner ℝ (e.symm !₂[1, deriv (upperGraphHeight K o e) x]) (normalVector a) = 0 := by
  let g := upperGraphHeight K o e
  let n := e (normalVector a)
  let f : ℝ → ℝ := fun y ↦ (y - x) * n 0 + (g y - g x) * n 1
  have hlocal : IsLocalMax f x := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    have hyproj : y ∈ horizontalProjection K o e := by
      rw [horizontalProjection_eq_Icc K o e]
      exact ⟨hy.1.le, hy.2.le⟩
    have hmem := upperGraphHeight_mem K o e hyproj
    have hsupport := ha (o + e.symm !₂[y, g y]) hmem
    rw [← e.inner_map_map] at hsupport
    simp only [map_sub, map_add, LinearIsometryEquiv.apply_symm_apply, PiLp.inner_apply,
      RCLike.inner_apply, conj_trivial, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, PiLp.sub_apply, PiLp.add_apply] at hsupport
    dsimp only [f, g, n]
    dsimp only [g] at hsupport
    nlinarith [hsupport]
  have hfderiv : HasDerivAt f (n 0 + deriv g x * n 1) x := by
    convert (((hasDerivAt_id x).sub_const x).mul_const (n 0)).add
      ((hdiff.hasDerivAt.sub_const (g x)).mul_const (n 1)) using 1
    · funext y
      rfl
    · simp [g]
  have hzero := hlocal.hasDerivAt_eq_zero hfderiv
  rw [← e.inner_map_map]
  simp only [LinearIsometryEquiv.apply_symm_apply, PiLp.inner_apply, RCLike.inner_apply,
    conj_trivial, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  dsimp only [g, n] at hzero ⊢
  nlinarith [hzero]

private theorem normalVector_injective : Function.Injective normalVector := by
  intro a b hab
  induction a using Real.Angle.induction_on with
  | _ a =>
    induction b using Real.Angle.induction_on with
    | _ b =>
      apply Real.Angle.cos_sin_inj
      · exact congrFun (congrArg WithLp.ofLp hab) 0
      · exact congrFun (congrArg WithLp.ofLp hab) 1

private theorem exteriorNormal_eq_of_orthogonal_of_interior_nonempty
    (K : ConvexBody Point) (hK : (interior (K : Set Point)).Nonempty)
    {p v : Point} (hv : v ≠ 0) {a b : Real.Angle}
    (ha : IsExteriorNormal K p a) (hb : IsExteriorNormal K p b)
    (hva : inner ℝ v (normalVector a) = 0)
    (hvb : inner ℝ v (normalVector b) = 0) : a = b := by
  let orientation : Orientation ℝ Point (Fin 2) :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation
  rcases EuclideanGeometry.eq_or_eq_neg_of_unit_orthogonal orientation hv (norm_normalVector a)
      (norm_normalVector b) hva hvb with hab | hab
  · exact normalVector_injective hab
  · exfalso
    obtain ⟨z, hz⟩ := hK
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
    let q := z + (ε / 2) • normalVector a
    have hq : q ∈ K := interior_subset (hball (by
      rw [Metric.mem_ball, dist_eq_norm]
      rw [show q - z = (ε / 2) • normalVector a by simp [q], norm_smul,
        norm_normalVector, Real.norm_eq_abs, abs_of_pos (div_pos hε (by norm_num))]
      norm_num
      linarith))
    have haz := ha z (interior_subset hz)
    have hbz := hb z (interior_subset hz)
    have hba : normalVector b = -normalVector a := by rw [hab]; simp
    rw [hba, inner_neg_right] at hbz
    have heq : inner ℝ (z - p) (normalVector a) = 0 := by linarith
    have haq := ha q hq
    have hqp : q - p = (z - p) + (ε / 2) • normalVector a := by
      dsimp only [q]
      module
    rw [hqp,
      inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq,
      norm_normalVector a, heq, zero_add] at haq
    have : ε / 2 ≤ 0 := by simpa using haq
    linarith

/-- A differentiable interior point of an upper boundary graph is regular. -/
theorem upperGraph_mem_regularBoundary (K : ConvexBody Point)
    (hK : (interior (K : Set Point)).Nonempty) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point)
    {x : ℝ} (hx : x ∈ Set.Ioo (horizontalBounds K o e).1 (horizontalBounds K o e).2)
    (hdiff : DifferentiableAt ℝ (upperGraphHeight K o e) x) :
    o + e.symm !₂[x, upperGraphHeight K o e x] ∈ regularBoundary K := by
  let p := o + e.symm !₂[x, upperGraphHeight K o e x]
  let a := vectorNormalAngle
    (e.symm !₂[-deriv (upperGraphHeight K o e) x, 1])
  have hxproj : x ∈ horizontalProjection K o e := by
    rw [horizontalProjection_eq_Icc K o e]
    exact ⟨hx.1.le, hx.2.le⟩
  have hp : p ∈ K := upperGraphHeight_mem K o e hxproj
  have ha : IsExteriorNormal K p a := upperGraph_deriv_isExteriorNormal K o e hx hdiff
  refine ⟨mem_frontier_of_mem_of_isExteriorNormal K hp ha, a, ha, ?_⟩
  intro b hb
  symm
  apply exteriorNormal_eq_of_orthogonal_of_interior_nonempty K hK
    (v := e.symm !₂[1, deriv (upperGraphHeight K o e) x])
  · intro hv
    have := congrFun (congrArg WithLp.ofLp (congrArg e hv)) 0
    simp at this
  · exact ha
  · exact hb
  · rw [normalVector_vectorNormalAngle]
    · rw [← e.inner_map_map]
      simp [PiLp.inner_apply, Fin.sum_univ_two]
    · intro hv
      have := congrFun (congrArg WithLp.ofLp (congrArg e hv)) 1
      simp at this
  · exact upperGraph_tangent_orthogonal_of_isExteriorNormal K o e hx hdiff (a := b) hb

/-- Points of an upper graph lying above nondifferentiability parameters. -/
def irregularUpperGraph (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) : Set Point :=
  (fun x ↦ o + e.symm !₂[x, upperGraphHeight K o e x]) ''
    {x | x ∈ Set.Ioo (horizontalBounds K o e).1 (horizontalBounds K o e).2 ∧
      ¬ DifferentiableAt ℝ (upperGraphHeight K o e) x}

/-- An irregular upper graph has zero one-dimensional Hausdorff measure. -/
theorem hausdorffMeasure_irregularUpperGraph_eq_zero (K : ConvexBody Point)
    (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) :
    Measure.hausdorffMeasure 1 (irregularUpperGraph K o e) = 0 := by
  exact MeasureTheory.hausdorffMeasure_coordinateGraph_nondifferentiable_eq_zero
    (locallyLipschitzOn_upperGraphHeight K o e) o e

private theorem eq_left_or_eq_right_or_mem_Ioo {a b x : ℝ} (hx : x ∈ Set.Icc a b) :
    x = a ∨ x = b ∨ x ∈ Set.Ioo a b := by
  rcases hx.1.eq_or_lt with h | h
  · exact Or.inl h.symm
  rcases hx.2.eq_or_lt with h' | h'
  · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr ⟨h, h'⟩)

private theorem irregularBoundary_subset_graphs_union_corners (K : ConvexBody Point)
    (hK : (interior (K : Set Point)).Nonempty) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) :
    frontier (K : Set Point) \ regularBoundary K ⊆
      irregularUpperGraph K o e ∪ (irregularUpperGraph K o (negCoordinates e) ∪
      (irregularUpperGraph K o (swapCoordinates e) ∪
      (irregularUpperGraph K o (negCoordinates (swapCoordinates e)) ∪
      coordinateCornerSet K o e))) := by
  intro p hp
  have hpK : p ∈ K := by
    change p ∈ (K : Set Point)
    rw [← K.isClosed.closure_eq]
    exact frontier_subset_closure hp.1
  let x := e (p - o) 0
  let y := e (p - o) 1
  have hxIcc : x ∈ Set.Icc (horizontalBounds K o e).1
      (horizontalBounds K o e).2 := by
    rw [← horizontalProjection_eq_Icc K o e]
    exact ⟨p, hpK, rfl⟩
  have hyIcc : y ∈ Set.Icc (horizontalBounds K o (swapCoordinates e)).1
      (horizontalBounds K o (swapCoordinates e)).2 := by
    rw [← horizontalProjection_eq_Icc K o (swapCoordinates e)]
    refine ⟨p, hpK, ?_⟩
    simp [y, swapCoordinates_apply_zero]
  rcases eq_left_or_eq_right_or_mem_Ioo hxIcc with hxleft | hxright | hxint
  · rcases eq_left_or_eq_right_or_mem_Ioo hyIcc with hyleft | hyright | hyint
    · right; right; right; right
      exact ⟨Or.inl (by simpa [x] using hxleft), Or.inl (by simpa [y] using hyleft)⟩
    · right; right; right; right
      exact ⟨Or.inl (by simpa [x] using hxleft), Or.inr (by simpa [y] using hyright)⟩
    · right; right; right; left
      let e' := negCoordinates (swapCoordinates e)
      let z := e' (p - o) 0
      have hzint : z ∈ Set.Ioo (horizontalBounds K o e').1
          (horizontalBounds K o e').2 := by
        rw [horizontalBounds_negCoordinates]
        change -y ∈ Set.Ioo (-(horizontalBounds K o (swapCoordinates e)).2)
          (-(horizontalBounds K o (swapCoordinates e)).1)
        exact ⟨neg_lt_neg hyint.2, neg_lt_neg hyint.1⟩
      have hgraph := eq_negSwapUpperGraph_of_horizontalCoordinate_eq_leftBound
        K o e hpK (by simpa [x] using hxleft)
      refine ⟨z, ⟨hzint, ?_⟩, hgraph.symm⟩
      intro hdiff
      apply hp.2
      rw [hgraph]
      exact upperGraph_mem_regularBoundary K hK o e' hzint hdiff
  · rcases eq_left_or_eq_right_or_mem_Ioo hyIcc with hyleft | hyright | hyint
    · right; right; right; right
      exact ⟨Or.inr (by simpa [x] using hxright), Or.inl (by simpa [y] using hyleft)⟩
    · right; right; right; right
      exact ⟨Or.inr (by simpa [x] using hxright), Or.inr (by simpa [y] using hyright)⟩
    · right; right; left
      let e' := swapCoordinates e
      let z := e' (p - o) 0
      have hzint : z ∈ Set.Ioo (horizontalBounds K o e').1
          (horizontalBounds K o e').2 := by simpa [e', z, y] using hyint
      have hgraph := eq_swapUpperGraph_of_horizontalCoordinate_eq_rightBound
        K o e hpK (by simpa [x] using hxright)
      refine ⟨z, ⟨hzint, ?_⟩, hgraph.symm⟩
      intro hdiff
      apply hp.2
      rw [hgraph]
      exact upperGraph_mem_regularBoundary K hK o e' hzint hdiff
  · obtain ⟨a, ha⟩ := exists_isExteriorNormal_of_mem_frontier K hK hp.1
    have hvertical : e (normalVector a) 1 ≠ 0 := by
      intro hzero
      rcases horizontalCoordinate_eq_endpoint_of_isExteriorNormal_of_vertical_eq_zero
        K o e hpK ha hzero with hleft | hright
      · exact hxint.1.ne' (by simpa [x] using hleft)
      · exact hxint.2.ne (by simpa [x] using hright)
    rcases lt_or_gt_of_ne hvertical with hneg | hpos
    · right; left
      let e' := negCoordinates e
      let z := e' (p - o) 0
      have hzint : z ∈ Set.Ioo (horizontalBounds K o e').1
          (horizontalBounds K o e').2 := by
        rw [horizontalBounds_negCoordinates]
        change -x ∈ Set.Ioo (-(horizontalBounds K o e).2)
          (-(horizontalBounds K o e).1)
        exact ⟨neg_lt_neg hxint.2, neg_lt_neg hxint.1⟩
      have hgraph := eq_upperCoordinateGraph_of_isExteriorNormal_of_pos K o e'
        hpK ha (by simpa [e'] using neg_pos.mpr hneg)
      refine ⟨z, ⟨hzint, ?_⟩, hgraph.symm⟩
      intro hdiff
      apply hp.2
      rw [hgraph]
      exact upperGraph_mem_regularBoundary K hK o e' hzint hdiff
    · left
      have hgraph := eq_upperCoordinateGraph_of_isExteriorNormal_of_pos K o e hpK ha hpos
      refine ⟨x, ⟨hxint, ?_⟩, ?_⟩
      · intro hdiff
        apply hp.2
        rw [hgraph]
        exact upperGraph_mem_regularBoundary K hK o e hxint hdiff
      · simpa [x] using hgraph.symm

/-- The irregular boundary of a planar convex body with nonempty interior has
zero one-dimensional Hausdorff measure. -/
theorem hausdorffMeasure_irregularBoundary_eq_zero (K : ConvexBody Point)
    (hK : (interior (K : Set Point)).Nonempty) :
    Measure.hausdorffMeasure 1
      (frontier (K : Set Point) \ regularBoundary K) = 0 := by
  let e : Point ≃ₗᵢ[ℝ] Point := LinearIsometryEquiv.refl ℝ Point
  let o : Point := 0
  apply measure_mono_null
    (irregularBoundary_subset_graphs_union_corners K hK o e)
  exact MeasureTheory.measure_union_null
    (hausdorffMeasure_irregularUpperGraph_eq_zero K o e)
    (MeasureTheory.measure_union_null
      (hausdorffMeasure_irregularUpperGraph_eq_zero K o (negCoordinates e))
      (MeasureTheory.measure_union_null
        (hausdorffMeasure_irregularUpperGraph_eq_zero K o (swapCoordinates e))
        (MeasureTheory.measure_union_null
          (hausdorffMeasure_irregularUpperGraph_eq_zero K o
            (negCoordinates (swapCoordinates e)))
          (hausdorffMeasure_coordinateCornerSet_eq_zero K o e))))

end MovingSofa
