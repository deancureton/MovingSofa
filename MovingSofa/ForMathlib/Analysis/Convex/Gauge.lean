import Mathlib.Analysis.Convex.Gauge
import Mathlib.Tactic

open Set
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A direction of positive gauge has a unique positive multiple on the frontier. -/
lemma Convex.existsUnique_pos_smul_mem_frontier_of_gauge_pos {s : Set E}
    (hs : Convex ℝ s) (h₀ : s ∈ nhds (0 : E)) {u : E} (hu : 0 < gauge s u) :
    ∃! r : ℝ, 0 < r ∧ r • u ∈ frontier s := by
  refine ⟨(gauge s u)⁻¹, ⟨inv_pos.mpr hu, ?_⟩, ?_⟩
  · apply (gauge_eq_one_iff_mem_frontier hs h₀).mp
    rw [gauge_smul_of_nonneg (inv_nonneg.mpr hu.le), smul_eq_mul, inv_mul_cancel₀ hu.ne']
  · intro r hr
    have h := (gauge_eq_one_iff_mem_frontier hs h₀).mpr hr.2
    rw [gauge_smul_of_nonneg hr.1.le, smul_eq_mul] at h
    simpa only [one_div] using (eq_div_iff hu.ne').mpr h

/-- Every nonzero direction has a unique positive multiple on the frontier of a bounded convex neighborhood of zero. -/
lemma Convex.existsUnique_pos_smul_mem_frontier {s : Set E}
    (hs : Convex ℝ s) (h₀ : s ∈ nhds (0 : E))
    (hb : Bornology.IsVonNBounded ℝ s) {u : E} (hu : u ≠ 0) :
    ∃! r : ℝ, 0 < r ∧ r • u ∈ frontier s :=
  hs.existsUnique_pos_smul_mem_frontier_of_gauge_pos h₀
    ((gauge_pos (absorbent_nhds_zero h₀) hb).mpr hu)

/-- Reciprocation is Lipschitz on real numbers bounded below by a positive constant. -/
lemma Real.dist_inv_le_of_pos_lower_bound {a b c : ℝ} (hc : 0 < c)
    (ha : c ≤ a) (hb : c ≤ b) :
    dist a⁻¹ b⁻¹ ≤ c⁻¹ ^ 2 * dist a b := by
  have ha₀ := hc.trans_le ha
  have hb₀ := hc.trans_le hb
  rw [dist_inv_inv₀ ha₀.ne' hb₀.ne', Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos ha₀, abs_of_pos hb₀]
  calc
    dist a b / (a * b) ≤ dist a b / (c * c) := by gcongr
    _ = c⁻¹ ^ 2 * dist a b := by ring

/-- The reciprocal of a positive uniformly bounded-below Lipschitz function is Lipschitz. -/
lemma LipschitzWith.inv_of_pos_lower_bound {X : Type*} [PseudoMetricSpace X]
    {f : X → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) {c : ℝ}
    (hc : 0 < c) (hbound : ∀ x, c ≤ f x) :
    LipschitzWith (Real.toNNReal (c⁻¹ ^ 2) * K) (fun x ↦ (f x)⁻¹) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    dist (f x)⁻¹ (f y)⁻¹ ≤ c⁻¹ ^ 2 * dist (f x) (f y) :=
      Real.dist_inv_le_of_pos_lower_bound hc (hbound x) (hbound y)
    _ ≤ c⁻¹ ^ 2 * ((K : ℝ) * dist x y) :=
      mul_le_mul_of_nonneg_left (hf.dist_le_mul x y) (sq_nonneg _)
    _ = _ := by
      rw [NNReal.coe_mul, Real.coe_toNNReal _ (sq_nonneg _)]
      ring

/-- The reciprocal gauge is Lipschitz on the unit sphere of a bounded convex neighborhood of zero. -/
lemma Convex.exists_lipschitzWith_inv_gauge_sphere {s : Set E}
    (hs : Convex ℝ s) (h₀ : s ∈ nhds (0 : E)) {R : ℝ} (hR : 0 < R)
    (hbound : s ⊆ Metric.closedBall 0 R) :
    ∃ C, LipschitzWith C (fun u : {u : E | ‖u‖ = 1} ↦ (gauge s u.val)⁻¹) := by
  obtain ⟨K, hK⟩ := hs.lipschitz_gauge h₀
  have hf : LipschitzWith K (fun u : {u : E | ‖u‖ = 1} ↦ gauge s u.val) :=
    by
      apply LipschitzWith.of_dist_le_mul
      intro u v
      exact hK.dist_le_mul u.val v.val
  have hlower (u : {u : E | ‖u‖ = 1}) : 1 / R ≤ gauge s u.val := by
    have hu : ‖(u : E)‖ = 1 := u.property
    calc
      1 / R = ‖u.val‖ / R := congrArg (fun r ↦ r / R) hu.symm
      _ ≤ gauge s u.val :=
        le_gauge_of_subset_closedBall (absorbent_nhds_zero h₀) hR.le hbound
  exact ⟨_, hf.inv_of_pos_lower_bound (one_div_pos.mpr hR) hlower⟩

/-- Radial gauge rescaling is Lipschitz on the unit sphere. -/
lemma Convex.exists_lipschitzWith_radial_gauge_sphere {s : Set E}
    (hs : Convex ℝ s) (h₀ : s ∈ nhds (0 : E)) {R : ℝ} (hR : 0 < R)
    (hbound : s ⊆ Metric.closedBall 0 R) :
    ∃ C, LipschitzWith C
      (fun u : {u : E | ‖u‖ = 1} ↦ (gauge s u.val)⁻¹ • u.val) := by
  obtain ⟨C, hC⟩ := hs.exists_lipschitzWith_inv_gauge_sphere h₀ hR hbound
  have hr (u : {u : E | ‖u‖ = 1}) : 0 ≤ (gauge s u.val)⁻¹ ∧
      (gauge s u.val)⁻¹ ≤ R := by
    have hu : ‖u.val‖ = 1 := u.property
    have hlower : 1 / R ≤ gauge s u.val := by
      calc
        1 / R = ‖u.val‖ / R := congrArg (fun r ↦ r / R) hu.symm
        _ ≤ _ := le_gauge_of_subset_closedBall (absorbent_nhds_zero h₀) hR.le hbound
    refine ⟨inv_nonneg.mpr (gauge_nonneg _), ?_⟩
    simpa only [one_div, inv_inv] using
      one_div_le_one_div_of_le (one_div_pos.mpr hR) hlower
  refine ⟨Real.toNNReal R + C, LipschitzWith.of_dist_le_mul fun u v ↦ ?_⟩
  have hv : ‖v.val‖ = 1 := v.property
  calc
    dist ((gauge s u.val)⁻¹ • u.val) ((gauge s v.val)⁻¹ • v.val) ≤
        dist ((gauge s u.val)⁻¹ • u.val) ((gauge s u.val)⁻¹ • v.val) +
        dist ((gauge s u.val)⁻¹ • v.val) ((gauge s v.val)⁻¹ • v.val) :=
      dist_triangle _ _ _
    _ = (gauge s u.val)⁻¹ * dist u v +
        dist (gauge s u.val)⁻¹ (gauge s v.val)⁻¹ := by
      rw [dist_smul₀, Real.norm_eq_abs, abs_of_nonneg (hr u).1]
      congr 1
      rw [dist_eq_norm, ← sub_smul, norm_smul, hv, mul_one, dist_eq_norm]
    _ ≤ R * dist u v + (C : ℝ) * dist u v :=
      add_le_add (mul_le_mul_of_nonneg_right (hr u).2 dist_nonneg) (hC.dist_le_mul u v)
    _ = _ := by rw [NNReal.coe_add, Real.coe_toNNReal _ hR.le]; ring
