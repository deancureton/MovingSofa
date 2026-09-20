import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Topology.MetricSpace.HausdorffDistance

open scoped ENNReal

/-- Support values of compact sets differ by at most their Hausdorff distance times the norm of
the direction. -/
theorem IsCompact.abs_csSup_inner_sub_le_hausdorffDist
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {S T : Set E} (hS : IsCompact S) (hneS : S.Nonempty)
    (hT : IsCompact T) (hneT : T.Nonempty) (u : E) :
    |sSup ((fun x ↦ inner ℝ x u) '' S) - sSup ((fun x ↦ inner ℝ x u) '' T)| ≤
      Metric.hausdorffDist S T * ‖u‖ := by
  obtain ⟨x, hxS, hx, hxmax⟩ := hS.exists_sSup_image_eq_and_ge
    (f := fun x : E ↦ inner ℝ x u) hneS
    (continuous_inner.comp (continuous_id.prodMk continuous_const)).continuousOn
  obtain ⟨y, hyT, hy⟩ := hT.exists_infDist_eq_dist hneT x
  obtain ⟨z, hzT, hz, hzmax⟩ := hT.exists_sSup_image_eq_and_ge
    (f := fun x : E ↦ inner ℝ x u) hneT
    (continuous_inner.comp (continuous_id.prodMk continuous_const)).continuousOn
  have hfin : Metric.hausdorffEDist S T ≠ ⊤ :=
    Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded hneS hneT
      hS.isBounded hT.isBounded
  have hdist : ‖x - y‖ ≤ Metric.hausdorffDist S T := by
    calc
      ‖x - y‖ = dist x y := (dist_eq_norm x y).symm
      _ = Metric.infDist x T := hy.symm
      _ ≤ Metric.hausdorffDist S T := Metric.infDist_le_hausdorffDist_of_mem hxS hfin
  have hupper : sSup ((fun x ↦ inner ℝ x u) '' S) -
      sSup ((fun x ↦ inner ℝ x u) '' T) ≤ Metric.hausdorffDist S T * ‖u‖ := by
    rw [hx, hz]
    calc
      inner ℝ x u - inner ℝ z u ≤ inner ℝ x u - inner ℝ y u :=
        sub_le_sub_left (hzmax y hyT) _
      _ = inner ℝ (x - y) u := by rw [inner_sub_left]
      _ ≤ |inner ℝ (x - y) u| := le_abs_self _
      _ ≤ ‖x - y‖ * ‖u‖ := by
        simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) (x - y) u
      _ ≤ Metric.hausdorffDist S T * ‖u‖ := by gcongr
  have hreverse : sSup ((fun x ↦ inner ℝ x u) '' T) -
      sSup ((fun x ↦ inner ℝ x u) '' S) ≤ Metric.hausdorffDist S T * ‖u‖ := by
    have hfin' : Metric.hausdorffEDist T S ≠ ⊤ :=
      Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded hneT hneS
        hT.isBounded hS.isBounded
    obtain ⟨x', hx'S, hx'⟩ := hS.exists_infDist_eq_dist hneS z
    have hdist' : ‖z - x'‖ ≤ Metric.hausdorffDist S T := by
      calc
        ‖z - x'‖ = dist z x' := (dist_eq_norm z x').symm
        _ = Metric.infDist z S := hx'.symm
        _ ≤ Metric.hausdorffDist T S :=
          Metric.infDist_le_hausdorffDist_of_mem hzT hfin'
        _ = Metric.hausdorffDist S T := Metric.hausdorffDist_comm
    rw [hz, hx]
    calc
      inner ℝ z u - inner ℝ x u ≤ inner ℝ z u - inner ℝ x' u :=
        sub_le_sub_left (hxmax x' hx'S) _
      _ = inner ℝ (z - x') u := by rw [inner_sub_left]
      _ ≤ |inner ℝ (z - x') u| := le_abs_self _
      _ ≤ ‖z - x'‖ * ‖u‖ := by
        simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) (z - x') u
      _ ≤ Metric.hausdorffDist S T * ‖u‖ := by gcongr
  rw [abs_le]
  constructor <;> linarith

/-- The support values of a compact set are Lipschitz in the direction, with constant equal to the
maximum norm of a point in the set. -/
theorem IsCompact.abs_csSup_inner_sub_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {S : Set E} (hS : IsCompact S) (hneS : S.Nonempty) (u v : E) :
    |sSup ((fun x ↦ inner ℝ x u) '' S) - sSup ((fun x ↦ inner ℝ x v) '' S)| ≤
      sSup (norm '' S) * ‖u - v‖ := by
  obtain ⟨x, hxS, hxu, hxu'⟩ := hS.exists_sSup_image_eq_and_ge
    (f := fun x : E ↦ inner ℝ x u) hneS
    (continuous_inner.comp (continuous_id.prodMk continuous_const)).continuousOn
  obtain ⟨y, hyS, hyv, hyv'⟩ := hS.exists_sSup_image_eq_and_ge
    (f := fun x : E ↦ inner ℝ x v) hneS
    (continuous_inner.comp (continuous_id.prodMk continuous_const)).continuousOn
  have hbound (z : E) (hz : z ∈ S) (w : E) :
      |inner ℝ z w| ≤ sSup (norm '' S) * ‖w‖ := by
    calc
      |inner ℝ z w| ≤ ‖z‖ * ‖w‖ := by
        simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) z w
      _ ≤ sSup (norm '' S) * ‖w‖ := by
        gcongr
        exact le_csSup (hS.bddAbove_image continuous_norm.continuousOn) ⟨z, hz, rfl⟩
  have huv : sSup ((fun x ↦ inner ℝ x u) '' S) -
      sSup ((fun x ↦ inner ℝ x v) '' S) ≤ sSup (norm '' S) * ‖u - v‖ := by
    rw [hxu, hyv]
    calc
      inner ℝ x u - inner ℝ y v ≤ inner ℝ x u - inner ℝ x v :=
        sub_le_sub_left (hyv' x hxS) _
      _ = inner ℝ x (u - v) := by rw [inner_sub_right]
      _ ≤ |inner ℝ x (u - v)| := le_abs_self _
      _ ≤ sSup (norm '' S) * ‖u - v‖ := hbound x hxS (u - v)
  have hvu : sSup ((fun x ↦ inner ℝ x v) '' S) -
      sSup ((fun x ↦ inner ℝ x u) '' S) ≤ sSup (norm '' S) * ‖u - v‖ := by
    rw [hyv, hxu]
    calc
      inner ℝ y v - inner ℝ x u ≤ inner ℝ y v - inner ℝ y u :=
        sub_le_sub_left (hxu' y hyS) _
      _ = inner ℝ y (v - u) := by rw [inner_sub_right]
      _ ≤ |inner ℝ y (v - u)| := le_abs_self _
      _ ≤ sSup (norm '' S) * ‖v - u‖ := hbound y hyS (v - u)
      _ = sSup (norm '' S) * ‖u - v‖ := by rw [norm_sub_rev]
  rw [abs_le]
  constructor <;> linarith

/-- A convex body in a real inner product space is the intersection of its supporting
half-spaces. -/
theorem ConvexBody.eq_iInter_halfSpaces
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : ConvexBody E) :
    (K : Set E) = ⋂ u ∈ {u : E | ‖u‖ = 1},
      {p : E | inner ℝ p u ≤ sSup ((fun x ↦ inner ℝ x u) '' (K : Set E))} := by
  apply Set.Subset.antisymm
  · intro p hp
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    intro u _
    obtain ⟨x, hx, hxmax, hmax⟩ := K.isCompact.exists_sSup_image_eq_and_ge
      (f := fun x : E ↦ inner ℝ x u) K.nonempty
      (continuous_inner.comp (continuous_id.prodMk continuous_const)).continuousOn
    rw [hxmax]
    exact hmax p hp
  · intro p hp
    by_contra hpK
    obtain ⟨q, hq, hqmin⟩ :=
      exists_norm_eq_iInf_of_complete_convex K.nonempty K.isCompact.isComplete K.convex p
    have hpq : p - q ≠ 0 := sub_ne_zero.mpr (fun h ↦ hpK (h ▸ hq))
    let u : E := ‖p - q‖⁻¹ • (p - q)
    have hnorm : 0 < ‖p - q‖ := norm_pos_iff.mpr hpq
    have hu : ‖u‖ = 1 := by simp [u, norm_smul, hnorm.ne']
    have hproj : ∀ y ∈ (K : Set E), inner ℝ (p - q) (y - q) ≤ 0 :=
      (norm_eq_iInf_iff_real_inner_le_zero K.convex hq).mp hqmin
    have hqmax : sSup ((fun x ↦ inner ℝ x u) '' (K : Set E)) = inner ℝ q u := by
      obtain ⟨x, hx, hxmax, hmax⟩ := K.isCompact.exists_sSup_image_eq_and_ge
        (f := fun x : E ↦ inner ℝ x u) K.nonempty
        (continuous_inner.comp (continuous_id.prodMk continuous_const)).continuousOn
      rw [hxmax]
      apply le_antisymm
      · dsimp [u]
        rw [inner_smul_right, inner_smul_right]
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hnorm.le)
        have h := hproj x hx
        have h' : inner ℝ (x - q) (p - q) ≤ 0 := by rwa [real_inner_comm]
        rw [inner_sub_left] at h'
        linarith
      · exact hmax q hq
    have hpu := Set.mem_iInter.mp (Set.mem_iInter.mp hp u) hu
    rw [hqmax] at hpu
    have hstrict : inner ℝ q u < inner ℝ p u := by
      dsimp [u]
      rw [inner_smul_right, inner_smul_right]
      have hself : 0 < inner ℝ (p - q) (p - q) := by
        rw [real_inner_self_eq_norm_sq]
        positivity
      rw [← sub_pos, ← mul_sub, ← inner_sub_left]
      exact mul_pos (inv_pos.mpr hnorm) hself
    exact (not_lt_of_ge hpu) hstrict
