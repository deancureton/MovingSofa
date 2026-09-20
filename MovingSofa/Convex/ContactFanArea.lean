import MovingSofa.Analysis.MeasureProducts
import MovingSofa.Classical.Area
import MovingSofa.ForMathlib.MeasureTheory.Measure.PlanarTriangle

/-!
# Area lower bound from ordered support contacts

A compact convex set `K` of the plane that contains a base point `L = (ℓ, 0)` and lies in the
closed quadrant `{(a, b) | ℓ ≤ a, 0 ≤ b}` has area at least the shoelace expression of any
finite fan `L, P₀, …, P_n` of support contacts taken at strictly increasing normal angles in
`[0, π)`.

Two ordered contacts span a nonnegatively oriented determinant over `L`: expanding the
support inequalities in coordinates turns `sin (β - α) · (P - L) × (Q - L)` into a sum of two
products of nonnegative factors. The fan triangles `convexHull ℝ {L, Pᵢ, Pᵢ₊₁}` therefore lie
in `K` with area one half of their determinant, and two of them can meet only along the line
through `L` and the contact they share, which is planar null. Finite additivity of the volume
off that null set and monotonicity give the bound. Repeated contacts, zero contact vectors and
collinear consecutive rays are allowed: a degenerate triangle simply has vanishing area.
-/

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- Two ordered support contacts of a set lying in the closed quadrant above a base point
have nonnegative oriented determinant over that base point. -/
theorem planeCrossProduct_sub_nonneg_of_support {K : Set Point} {L P Q : Point}
    (hL : L ∈ K) (hquadrant : ∀ p ∈ K, L 0 ≤ p 0 ∧ 0 ≤ p 1)
    {α β : ℝ} (hα : 0 ≤ α) (hαβ : α < β) (hβ : β < Real.pi)
    (hP : P ∈ K) (hQ : Q ∈ K)
    (hPs : ∀ x ∈ K, inner ℝ x (normalVector (α : Real.Angle)) ≤
      inner ℝ P (normalVector (α : Real.Angle)))
    (hQs : ∀ x ∈ K, inner ℝ x (normalVector (β : Real.Angle)) ≤
      inner ℝ Q (normalVector (β : Real.Angle))) :
    0 ≤ planeCrossProduct (P - L) (Q - L) := by
  have hsβ : 0 < Real.sin β := Real.sin_pos_of_pos_of_lt_pi (hα.trans_lt hαβ) hβ
  have hsα : 0 ≤ Real.sin α := Real.sin_nonneg_of_nonneg_of_le_pi hα (by linarith)
  have hsδ : 0 < Real.sin β * Real.cos α - Real.cos β * Real.sin α := by
    have h := Real.sin_pos_of_pos_of_lt_pi (x := β - α) (by linarith) (by linarith)
    rwa [Real.sin_sub] at h
  have hz : 0 ≤ (P 0 - Q 0) * Real.cos α + (P 1 - Q 1) * Real.sin α := by
    have h := hPs Q hQ
    rw [inner_normalVector_real, inner_normalVector_real] at h
    linarith
  have hk : 0 ≤ (Q 0 - P 0) * Real.cos β + (Q 1 - P 1) * Real.sin β := by
    have h := hQs P hP
    rw [inner_normalVector_real, inner_normalVector_real] at h
    linarith
  have hB : 0 ≤ (Q 0 - L 0) * Real.cos β + (Q 1 - L 1) * Real.sin β := by
    have h := hQs L hL
    rw [inner_normalVector_real, inner_normalVector_real] at h
    linarith
  have hq0 : 0 ≤ Q 0 - L 0 := sub_nonneg.mpr (hquadrant Q hQ).1
  have hc : 0 ≤ (Q 0 - L 0) * Real.cos α + (Q 1 - L 1) * Real.sin α := by
    have hid : Real.sin β * ((Q 0 - L 0) * Real.cos α + (Q 1 - L 1) * Real.sin α)
        = Real.sin α * ((Q 0 - L 0) * Real.cos β + (Q 1 - L 1) * Real.sin β)
          + (Real.sin β * Real.cos α - Real.cos β * Real.sin α) * (Q 0 - L 0) := by
      ring
    nlinarith [mul_nonneg hsα hB, mul_nonneg hsδ.le hq0]
  have hcross : planeCrossProduct (P - L) (Q - L)
      = (P 0 - L 0) * (Q 1 - L 1) - (P 1 - L 1) * (Q 0 - L 0) := by
    simp [planeCrossProduct]
  have hid2 : (Real.sin β * Real.cos α - Real.cos β * Real.sin α) *
      ((P 0 - L 0) * (Q 1 - L 1) - (P 1 - L 1) * (Q 0 - L 0))
      = ((Q 0 - L 0) * Real.cos α + (Q 1 - L 1) * Real.sin α) *
          ((Q 0 - P 0) * Real.cos β + (Q 1 - P 1) * Real.sin β)
        + ((P 0 - Q 0) * Real.cos α + (P 1 - Q 1) * Real.sin α) *
          ((Q 0 - L 0) * Real.cos β + (Q 1 - L 1) * Real.sin β) := by
    ring
  rw [hcross]
  nlinarith [mul_nonneg hc hk, mul_nonneg hz hB]

theorem supportContact_fan_area (K : Set Point) (hK : K.Nonempty)
    (hcK : IsCompact K) (hvK : Convex ℝ K) (L : Point) (hL : L ∈ K)
    (hLy : L 1 = 0) (hquadrant : ∀ p ∈ K, L 0 ≤ p 0 ∧ 0 ≤ p 1)
    (n : ℕ) (hn : 1 ≤ n) (θ : Fin (n + 1) → ℝ)
    (hθ : StrictMono θ) (hθrange : ∀ i, 0 ≤ θ i ∧ θ i < Real.pi)
    (P : Fin (n + 1) → Point) (hP : ∀ i, P i ∈ K)
    (hsupport : ∀ i q, q ∈ K →
      inner ℝ q (normalVector (θ i : Real.Angle)) ≤
        inner ℝ (P i) (normalVector (θ i : Real.Angle))) :
    0 ≤ (1 / 2 : ℝ) * ∑ i : Fin n,
      planeCrossProduct (P i.castSucc - L) (P i.succ - L) ∧
    (1 / 2 : ℝ) * (∑ i : Fin n,
      planeCrossProduct (P i.castSucc - L) (P i.succ - L)) ≤ ClassicalResults.area K := by
  have hquad : ∀ x ∈ K, 0 ≤ (x - L) 0 ∧ 0 ≤ (x - L) 1 := by
    intro x hx
    obtain ⟨h1, h2⟩ := hquadrant x hx
    exact ⟨by simpa using sub_nonneg.mpr h1, by simpa [hLy] using h2⟩
  have hmono : ∀ i j : Fin (n + 1), i ≤ j → 0 ≤ planeCrossProduct (P i - L) (P j - L) := by
    intro i j hij
    rcases eq_or_lt_of_le hij with rfl | hlt
    · simp
    · exact planeCrossProduct_sub_nonneg_of_support hL hquadrant (hθrange i).1 (hθ hlt)
        (hθrange j).2 (hP i) (hP j) (fun x hx ↦ hsupport i x hx) (fun x hx ↦ hsupport j x hx)
  have hcnn : ∀ i : Fin n, 0 ≤ planeCrossProduct (P i.castSucc - L) (P i.succ - L) :=
    fun i ↦ hmono _ _ Fin.castSucc_lt_succ.le
  have hsumnn : 0 ≤ ∑ i : Fin n, planeCrossProduct (P i.castSucc - L) (P i.succ - L) :=
    Finset.sum_nonneg fun i _ ↦ hcnn i
  refine ⟨by linarith, ?_⟩
  set T : Fin n → Set Point := fun i ↦ convexHull ℝ {L, P i.castSucc, P i.succ} with hTdef
  have hTsub : ∀ i, T i ⊆ K := by
    intro i
    refine convexHull_min ?_ hvK
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    exacts [hL, hP _, hP _]
  have hTvol : ∀ i, volume (T i) = ENNReal.ofReal
      ((1 / 2 : ℝ) * planeCrossProduct (P i.castSucc - L) (P i.succ - L)) := by
    intro i
    have hpos := hcnn i
    simp only [planeCrossProduct] at hpos
    simp only [hTdef, EuclideanSpace.volume_convexHull_triple]
    congr 1
    rw [abs_of_nonneg (by linarith)]
    simp only [planeCrossProduct]
    ring
  have hTmeas : ∀ i, NullMeasurableSet (T i) volume := by
    intro i
    refine (IsCompact.measurableSet ?_).nullMeasurableSet
    exact (((Set.finite_singleton _).insert _).insert _).isCompact_convexHull ℝ
  have hsector : ∀ i : Fin n, T i ⊆ {x : Point |
      0 ≤ planeCrossProduct (P i.castSucc - L) (x - L) ∧
      0 ≤ planeCrossProduct (x - L) (P i.succ - L)} := by
    intro i
    refine convexHull_min ?_ (convex_setOf_planeCrossProduct_fan _ _ _)
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨by simp, by simp⟩
    · exact ⟨by simp, hcnn i⟩
    · exact ⟨hcnn i, by simp⟩
  have hdisj : Pairwise (Function.onFun (AEDisjoint volume) T) := by
    have hkey : ∀ i j : Fin n, i < j → volume (T i ∩ T j) = 0 := by
      intro i j hij
      rcases eq_or_lt_of_le (hcnn i) with h0 | h0
      · exact measure_mono_null Set.inter_subset_left (by rw [hTvol i, ← h0]; simp)
      rcases eq_or_lt_of_le (hcnn j) with h1 | h1
      · exact measure_mono_null Set.inter_subset_right (by rw [hTvol j, ← h1]; simp)
      have hne2 : P j.castSucc - L ≠ 0 := by
        intro h
        rw [h] at h1
        simp [planeCrossProduct] at h1
      have hne1 : P i.succ - L ≠ 0 := by
        intro h
        rw [h] at h0
        simp [planeCrossProduct] at h0
      refine measure_mono_null ?_ (volume_setOf_planeCrossProduct_sub_eq_zero hne1 L)
      rintro x ⟨hxi, hxj⟩
      have hxK : x ∈ K := hTsub i hxi
      have h2 := (hsector i hxi).2
      have h3 := (hsector j hxj).1
      have hle : i.succ ≤ j.castSucc := by
        have hij' : (i : ℕ) < (j : ℕ) := hij
        rw [Fin.le_def]
        simp only [Fin.val_succ, Fin.val_castSucc]
        omega
      have h5 : 0 ≤ planeCrossProduct (P i.succ - L) (x - L) :=
        planeCrossProduct_nonneg_trans hne2
          (hquad _ (hP _)).1 (hquad _ (hP _)).2 (hquad _ (hP _)).1 (hquad _ (hP _)).2
          (hquad x hxK).1 (hquad x hxK).2 (hmono _ _ hle) h3
      show planeCrossProduct (P i.succ - L) (x - L) = 0
      rw [planeCrossProduct_swap (x - L)] at h2
      linarith
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hkey i j h
    · show volume (T i ∩ T j) = 0
      rw [Set.inter_comm]
      exact hkey j i h
  have hunion : ∑ i : Fin n, volume (T i) ≤ volume K := by
    have h := measure_iUnion₀ (μ := volume) hdisj hTmeas
    rw [tsum_fintype] at h
    rw [← h]
    exact measure_mono (Set.iUnion_subset hTsub)
  have hgoal : ENNReal.ofReal ((1 / 2 : ℝ) * ∑ i : Fin n,
      planeCrossProduct (P i.castSucc - L) (P i.succ - L)) ≤ volume K := by
    rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ by linarith [hcnn i])]
    simpa only [hTvol] using hunion
  exact (ENNReal.ofReal_le_iff_le_toReal hcK.measure_lt_top.ne).mp hgoal

end MovingSofa
