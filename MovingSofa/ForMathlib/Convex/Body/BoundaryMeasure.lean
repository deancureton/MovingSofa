import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Hausdorff

noncomputable section

open MeasureTheory
open scoped ENNReal Pointwise Topology

namespace ConvexBody

private abbrev Plane := EuclideanSpace ℝ (Fin 2)

private def unitCircleParam (t : ℝ) : Plane :=
  WithLp.toLp 2 (![Real.cos t, Real.sin t] : Fin 2 → ℝ)

private theorem lipschitzWith_unitCircleParam :
    LipschitzWith 2 unitCircleParam := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  rw [dist_eq_norm]
  rw [Real.dist_eq]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by positivity) (abs_nonneg _))).mp
  rw [EuclideanSpace.norm_sq_eq]
  simp only [unitCircleParam, PiLp.sub_apply, Fin.sum_univ_two, Real.norm_eq_abs,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  have hc : |Real.cos x - Real.cos y| ≤ |x - y| := by
    exact Real.abs_cos_sub_cos_le x y
  have hs : |Real.sin x - Real.sin y| ≤ |x - y| := by
    exact Real.abs_sin_sub_sin_le x y
  have hxy : 0 ≤ |x - y| := abs_nonneg _
  have hc_sq := sq_le_sq₀ (abs_nonneg _) hxy |>.mpr hc
  have hs_sq := sq_le_sq₀ (abs_nonneg _) hxy |>.mpr hs
  norm_num
  nlinarith [sq_abs (Real.cos x - Real.cos y), sq_abs (Real.sin x - Real.sin y)]

private theorem hausdorffMeasure_one_sphere_lt_top :
    Measure.hausdorffMeasure 1 (Metric.sphere (0 : Plane) 1) < ⊤ := by
  have hsphere : Metric.sphere (0 : Plane) 1 ⊆
      unitCircleParam '' Set.Icc (-Real.pi) Real.pi := by
    intro p hp
    have hnorm : ‖p‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hp
    let z : ℂ := ⟨p 0, p 1⟩
    have hzNorm : ‖z‖ = 1 := by
      rw [Complex.norm_def, show Complex.normSq z = ‖p‖ ^ 2 by
        rw [EuclideanSpace.norm_sq_eq]
        simp [z, Complex.normSq_apply, Fin.sum_univ_two, pow_two, Real.norm_eq_abs]]
      simp [hnorm]
    have hz : z ≠ 0 := by
      intro hz
      simp [hz] at hzNorm
    refine ⟨z.arg, ⟨(Complex.neg_pi_lt_arg z).le, Complex.arg_le_pi z⟩, ?_⟩
    ext i
    fin_cases i
    · simpa [unitCircleParam, z, hzNorm] using Complex.cos_arg hz
    · simpa [unitCircleParam, z, hzNorm] using Complex.sin_arg z
  calc
    Measure.hausdorffMeasure 1 (Metric.sphere (0 : Plane) 1) ≤
        Measure.hausdorffMeasure 1 (unitCircleParam '' Set.Icc (-Real.pi) Real.pi) :=
      measure_mono hsphere
    _ ≤ ((2 : NNReal) : ENNReal) ^ (1 : ℝ) *
        Measure.hausdorffMeasure 1 (Set.Icc (-Real.pi) Real.pi) :=
      lipschitzWith_unitCircleParam.hausdorffMeasure_image_le (by positivity) _
    _ < ⊤ := by
      rw [hausdorffMeasure_real, Real.volume_Icc]
      finiteness

private theorem image_gaugeRescale_unitSphere_eq_frontier {s : Set Plane}
    (hconv : Convex ℝ s) (h₀ : s ∈ nhds (0 : Plane)) (hbounded : Bornology.IsBounded s)
    (hclosed : IsClosed s) :
    gaugeRescale (Metric.ball 0 1) s '' Metric.sphere 0 1 = frontier s := by
  have hvnb : Bornology.IsVonNBounded ℝ s :=
    NormedSpace.isVonNBounded_of_isBounded ℝ hbounded
  let h := gaugeRescaleHomeomorph (Metric.ball (0 : Plane) 1) s
    (convex_ball 0 1) (Metric.ball_mem_nhds 0 zero_lt_one)
    (NormedSpace.isVonNBounded_ball ℝ Plane 1) hconv h₀ hvnb
  change h '' Metric.sphere 0 1 = frontier s
  rw [← frontier_ball, ← closure_sdiff_interior, Set.image_sdiff h.injective]
  rw [image_gaugeRescaleHomeomorph_closure, image_gaugeRescaleHomeomorph_interior]
  rw [hclosed.closure_eq]
  · simpa [hclosed.closure_eq] using closure_sdiff_interior s
  · norm_num

private theorem exists_lipschitzOnWith_gaugeRescale_unitSphere {s : Set Plane}
    (hconv : Convex ℝ s) (h₀ : s ∈ nhds (0 : Plane)) (hbounded : Bornology.IsBounded s) :
    ∃ C, LipschitzOnWith C (gaugeRescale (Metric.ball 0 1) s) (Metric.sphere 0 1) := by
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.mp h₀
  obtain ⟨B, hB⟩ := hbounded.exists_norm_le
  let R : ℝ := |B| + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hsR : s ⊆ Metric.closedBall (0 : Plane) R := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (hB x hx).trans (by dsimp [R]; linarith [le_abs_self B])
  have habs : Absorbent ℝ s := absorbent_nhds_zero h₀
  let rn : NNReal := ⟨r, hr.le⟩
  have hg : LipschitzWith rn⁻¹ (gauge s) := hconv.lipschitzWith_gauge hr hrs
  let C : NNReal := ⟨R + (rn⁻¹ : ℝ) * R ^ 2, by positivity⟩
  refine ⟨C, ?_⟩
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  have hnx : ‖x‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hx
  have hny : ‖y‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hy
  have hgx : 1 / R ≤ gauge s x := by
    simpa [hnx] using (le_gauge_of_subset_closedBall habs hR.le hsR : ‖x‖ / R ≤ gauge s x)
  have hgy : 1 / R ≤ gauge s y := by
    simpa [hny] using (le_gauge_of_subset_closedBall habs hR.le hsR : ‖y‖ / R ≤ gauge s y)
  have hgxpos : 0 < gauge s x := (div_pos one_pos hR).trans_le hgx
  have hgypos : 0 < gauge s y := (div_pos one_pos hR).trans_le hgy
  have hinvx : (gauge s x)⁻¹ ≤ R := by
    rw [inv_le_comm₀ hgxpos hR]
    simpa [div_eq_inv_mul] using hgx
  have hinvy : (gauge s y)⁻¹ ≤ R := by
    rw [inv_le_comm₀ hgypos hR]
    simpa [div_eq_inv_mul] using hgy
  have hginv : dist (gauge s x)⁻¹ (gauge s y)⁻¹ ≤
      (rn⁻¹ : ℝ) * R ^ 2 * dist x y := by
    rw [dist_inv_inv₀ hgxpos.ne' hgypos.ne']
    have hdist := hg.dist_le_mul x y
    have hprod : 1 / R ^ 2 ≤ ‖gauge s x‖ * ‖gauge s y‖ := by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hgxpos, abs_of_pos hgypos]
      calc
        1 / R ^ 2 = (1 / R) * (1 / R) := by ring_nf
        _ ≤ gauge s x * gauge s y :=
          mul_le_mul hgx hgy (div_nonneg one_pos.le hR.le) hgxpos.le
    calc
      dist (gauge s x) (gauge s y) / (‖gauge s x‖ * ‖gauge s y‖) ≤
          dist (gauge s x) (gauge s y) / (1 / R ^ 2) := by
        exact div_le_div_of_nonneg_left (dist_nonneg) (by positivity) hprod
      _ ≤ ((rn⁻¹ : ℝ) * dist x y) / (1 / R ^ 2) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        simpa [NNReal.coe_inv] using hdist
      _ = (rn⁻¹ : ℝ) * R ^ 2 * dist x y := by field_simp
  change dist ((gauge (Metric.ball 0 1) x / gauge s x) • x)
      ((gauge (Metric.ball 0 1) y / gauge s y) • y) ≤ (C : ℝ) * dist x y
  simp_rw [gauge_ball (by positivity : (0 : ℝ) ≤ 1)]
  rw [hnx, hny]
  simp only [inv_one, one_div]
  rw [dist_eq_norm]
  calc
    ‖(gauge s x)⁻¹ • x - (gauge s y)⁻¹ • y‖ ≤
        ‖(gauge s x)⁻¹ • (x - y)‖ +
          ‖((gauge s x)⁻¹ - (gauge s y)⁻¹) • y‖ := by
      have heq : (gauge s x)⁻¹ • x - (gauge s y)⁻¹ • y =
          (gauge s x)⁻¹ • (x - y) +
            ((gauge s x)⁻¹ - (gauge s y)⁻¹) • y := by module
      rw [heq]
      exact norm_add_le _ _
    _ ≤ R * dist x y + ((rn⁻¹ : ℝ) * R ^ 2 * dist x y) := by
      simp only [norm_smul, Real.norm_eq_abs, dist_eq_norm]
      have hix : |(gauge s x)⁻¹| ≤ R := by rw [abs_of_pos (inv_pos.mpr hgxpos)]; exact hinvx
      have hid : |(gauge s x)⁻¹ - (gauge s y)⁻¹| ≤
          (rn⁻¹ : ℝ) * R ^ 2 * ‖x - y‖ := by simpa [dist_eq_norm] using hginv
      rw [hny, mul_one]
      exact add_le_add (mul_le_mul_of_nonneg_right hix (norm_nonneg _)) hid
    _ = (C : ℝ) * dist x y := by
      change _ = (R + (rn⁻¹ : ℝ) * R ^ 2) * dist x y
      ring

private theorem hausdorffMeasure_frontier_lt_top_of_mem_nhds_zero {s : Set Plane}
    (hconv : Convex ℝ s) (h₀ : s ∈ nhds (0 : Plane)) (hcompact : IsCompact s) :
    Measure.hausdorffMeasure 1 (frontier s) < ⊤ := by
  obtain ⟨C, hC⟩ :=
    exists_lipschitzOnWith_gaugeRescale_unitSphere hconv h₀ hcompact.isBounded
  rw [← image_gaugeRescale_unitSphere_eq_frontier hconv h₀ hcompact.isBounded hcompact.isClosed]
  refine (hC.hausdorffMeasure_image_le (by positivity)).trans_lt ?_
  exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity) (by simp))
    hausdorffMeasure_one_sphere_lt_top

/-- The frontier of a planar convex body with nonempty interior has finite
one-dimensional Hausdorff measure. -/
theorem hausdorffMeasure_frontier_lt_top
    (K : ConvexBody (EuclideanSpace ℝ (Fin 2)))
    (hint : (interior (K : Set (EuclideanSpace ℝ (Fin 2)))).Nonempty) :
    Measure.hausdorffMeasure 1
      (frontier (K : Set (EuclideanSpace ℝ (Fin 2)))) < ⊤ := by
  obtain ⟨c, hc⟩ := hint
  let s : Set Plane := -c +ᵥ (K : Set Plane)
  have hsconv : Convex ℝ s := K.convex.vadd (-c)
  have hscompact : IsCompact s := by
    change IsCompact ((fun x : Plane ↦ -c + x) '' (K : Set Plane))
    exact K.isCompact.image (continuous_const.add continuous_id)
  have hs₀ : s ∈ nhds (0 : Plane) := by
    rw [← mem_interior_iff_mem_nhds]
    change (0 : Plane) ∈ interior (-c +ᵥ (K : Set Plane))
    rw [interior_vadd]
    simpa [Set.mem_vadd_set_iff_neg_vadd_mem] using hc
  have hsfinite := hausdorffMeasure_frontier_lt_top_of_mem_nhds_zero hsconv hs₀ hscompact
  have himage : (fun z : Plane ↦ c + z) '' frontier s = frontier (K : Set Plane) := by
    calc
      (fun z : Plane ↦ c + z) '' frontier s =
          frontier ((fun z : Plane ↦ c + z) '' s) :=
        (Homeomorph.addLeft c).image_frontier s
      _ = frontier (K : Set Plane) := by
        congr 1
        ext x
        simp [s, Set.mem_vadd_set_iff_neg_vadd_mem]
  have hisom : Isometry (fun z : Plane ↦ c + z) := by
    intro x y
    simp
  rw [← himage, hisom.hausdorffMeasure_image (Or.inl zero_le_one)]
  exact hsfinite


end ConvexBody
