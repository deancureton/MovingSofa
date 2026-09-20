import MovingSofa.Polygon.Polyline.Displacement
import MovingSofa.ForMathlib.Algebra.Order.Fin

noncomputable section

namespace MovingSofa

/-- A leftward edge displacement is its length times its oriented tangent. -/
theorem sub_eq_dist_smul_tangentVector {a b : Point} {t : ℝ}
    (ht : t ∈ Set.Ioo 0 Real.pi) (hab : a 0 < b 0)
    (horth : inner ℝ (b - a) (normalVector (t : Real.Angle)) = 0) :
    a - b = dist a b • tangentVector (t : Real.Angle) := by
  let r := inner ℝ (b - a) (tangentVector (t : Real.Angle))
  have hvec : r • tangentVector (t : Real.Angle) = b - a := by
    simpa only [horth, zero_smul, zero_add] using
      inner_normalVector_smul_add_inner_tangentVector_smul (b - a) (t : Real.Angle)
  have hcoord : -(r * Real.sin t) = b 0 - a 0 := by
    have h := congrArg (fun p : Point ↦ p 0) hvec
    simpa [tangentVector, frame] using h
  have hdist := dist_mul_sin_eq_fst_sub_of_inner_sub_eq_zero ht hab horth
  have hr : r = -dist a b := by
    have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
    nlinarith
  rw [hr, neg_smul] at hvec
  simpa only [neg_neg, neg_sub] using (congrArg Neg.neg hvec).symm

/-- Every point of a polyline satisfies the bound by positive projected edge increments. -/
theorem XMonotonePolylineData.inner_le_endpoint_add_sum_pos
    (p : XMonotonePolylineData) (u : Point) {q : Point} (hq : q ∈ p.carrier) :
    inner ℝ q u ≤ inner ℝ (p.vertices (Fin.last p.edges)) u +
      ∑ i : Fin p.edges, max (inner ℝ (p.vertices i.castSucc - p.vertices i.succ) u) 0 := by
  have hvertex (i : Fin (p.edges + 1)) :=
    Fin.apply_le_last_add_sum_max_sub (fun i ↦ inner ℝ (p.vertices i) u) i
  simp only [← inner_sub_left] at hvertex
  obtain ⟨i, hqi⟩ := Set.mem_iUnion.mp hq
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hqi
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have h₁ := mul_le_mul_of_nonneg_left (hvertex i.castSucc) ha
  have h₂ := mul_le_mul_of_nonneg_left (hvertex i.succ) hb
  have h := add_le_add h₁ h₂
  rwa [← add_mul, hab, one_mul] at h

/-- Grouping edge lengths by their unique normal preserves every weighted sum. -/
theorem XMonotonePolylineData.sum_normal_lengths_mul
    (p : XMonotonePolylineData) (D : Finset ℝ) (g : ℝ → ℝ)
    (hD : ∀ t ∈ D, t ∈ Set.Ioo 0 Real.pi)
    (t : Fin p.edges → ℝ) (ht : ∀ i, t i ∈ D)
    (horth : ∀ i, inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
      (normalVector (t i : Real.Angle)) = 0) :
    ∑ u ∈ D, (∑ i : Fin p.edges,
      if inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
        (normalVector (u : Real.Angle)) = 0 then
        dist (p.vertices i.castSucc) (p.vertices i.succ) else 0) * g u =
      ∑ i : Fin p.edges, dist (p.vertices i.castSucc) (p.vertices i.succ) * g (t i) := by
  classical
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single (t i)]
  · rw [ite_eq_left (horth i)]
  · intro u hu hut
    have hne : inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
        (normalVector (u : Real.Angle)) ≠ 0 := by
      intro hzero
      exact hut (eq_of_inner_sub_normalVector_eq_zero (hD u hu) (hD _ (ht i))
        (p.increasing i.castSucc_lt_succ) hzero (horth i))
    simp [hne]
  · exact fun hnot ↦ (hnot (ht i)).elim

/-- Positive normal projections bound every point of a polyline by its right endpoint. -/
theorem XMonotonePolylineData.inner_le_endpoint_add_sum_normal_lengths
    (p : XMonotonePolylineData) (D : Finset ℝ)
    (hD : ∀ t ∈ D, t ∈ Set.Ioo 0 Real.pi)
    (hlabels : ∀ i : Fin p.edges, ∃ t ∈ D,
      inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
        (normalVector (t : Real.Angle)) = 0)
    (s : ℝ) {q : Point} (hq : q ∈ p.carrier) :
    inner ℝ q (normalVector (s : Real.Angle)) ≤
      inner ℝ (p.vertices (Fin.last p.edges)) (normalVector (s : Real.Angle)) +
      ∑ u ∈ D, (∑ i : Fin p.edges,
        if inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
          (normalVector (u : Real.Angle)) = 0 then
          dist (p.vertices i.castSucc) (p.vertices i.succ) else 0) *
        max (Real.sin (s - u)) 0 := by
  classical
  choose t ht horth using hlabels
  rw [p.sum_normal_lengths_mul D (fun u ↦ max (Real.sin (s - u)) 0) hD t ht horth]
  have h := p.inner_le_endpoint_add_sum_pos (normalVector (s : Real.Angle)) hq
  convert h using 2
  apply Finset.sum_congr rfl
  intro i _
  rw [sub_eq_dist_smul_tangentVector (hD _ (ht i))
    (p.increasing i.castSucc_lt_succ) (horth i), real_inner_smul_left,
    inner_tangentVector_normalVector_real, mul_max_of_nonneg _ _ dist_nonneg, mul_zero]

end MovingSofa
