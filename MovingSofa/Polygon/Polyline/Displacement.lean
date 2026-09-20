import MovingSofa.Polygon.Polyline.Basic
import MovingSofa.Geometry.Frame
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

noncomputable section

namespace MovingSofa

/-- The horizontal displacement of a rightward edge is its length times the sine of its normal. -/
lemma dist_mul_sin_eq_fst_sub_of_inner_sub_eq_zero {a b : Point} {t : ℝ}
    (ht : t ∈ Set.Ioo 0 Real.pi) (hab : a 0 < b 0)
    (horth : inner ℝ (b - a) (normalVector (t : Real.Angle)) = 0) :
    dist a b * Real.sin t = b 0 - a 0 := by
  let r := inner ℝ (b - a) (tangentVector (t : Real.Angle))
  have hvec : r • tangentVector (t : Real.Angle) = b - a := by
    simpa only [horth, zero_smul, zero_add] using
      inner_normalVector_smul_add_inner_tangentVector_smul (b - a) (t : Real.Angle)
  have hcoord : -(r * Real.sin t) = b 0 - a 0 := by
    have h := congrArg (fun p : Point ↦ p 0) hvec
    simpa [tangentVector, frame] using h
  have hsin := Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
  have hr : r < 0 := by nlinarith
  have hn : ‖tangentVector (t : Real.Angle)‖ = 1 := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
    rw [EuclideanSpace.norm_sq_eq]
    simp [tangentVector, frame, Fin.sum_univ_two, Real.sin_sq_add_cos_sq]
  have hdist : dist a b = -r := by
    rw [dist_comm, dist_eq_norm, ← hvec, norm_smul, hn, mul_one,
      Real.norm_eq_abs, abs_of_neg hr]
  rw [hdist]
  linarith

/-- The sine-weighted edge lengths telescope to the horizontal endpoint displacement. -/
lemma XMonotonePolylineData.sum_dist_mul_sin
    (p : XMonotonePolylineData) (t : Fin p.edges → ℝ)
    (ht : ∀ i, t i ∈ Set.Ioo 0 Real.pi)
    (horth : ∀ i, inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
      (normalVector (t i : Real.Angle)) = 0) :
    ∑ i : Fin p.edges,
      dist (p.vertices i.castSucc) (p.vertices i.succ) * Real.sin (t i) =
        p.vertices (Fin.last p.edges) 0 - p.vertices 0 0 := by
  have hedge (i : Fin p.edges) := dist_mul_sin_eq_fst_sub_of_inner_sub_eq_zero
    (ht i) (p.increasing i.castSucc_lt_succ) (horth i)
  simp_rw [hedge]
  rw [Finset.sum_sub_distrib]
  have hfirst := Fin.sum_univ_succ (fun i : Fin (p.edges + 1) ↦ p.vertices i 0)
  have hlast := Fin.sum_univ_castSucc (fun i : Fin (p.edges + 1) ↦ p.vertices i 0)
  linarith

/-- A nonvertical segment has at most one normal angle strictly between zero and pi. -/
lemma eq_of_inner_sub_normalVector_eq_zero {a b : Point} {s t : ℝ}
    (hs : s ∈ Set.Ioo 0 Real.pi) (ht : t ∈ Set.Ioo 0 Real.pi)
    (hab : a 0 < b 0)
    (horths : inner ℝ (b - a) (normalVector (s : Real.Angle)) = 0)
    (hortht : inner ℝ (b - a) (normalVector (t : Real.Angle)) = 0) : s = t := by
  have hs' : (b 0 - a 0) * Real.cos s + (b 1 - a 1) * Real.sin s = 0 := by
    simpa [normalVector, frame, PiLp.inner_apply, mul_comm] using horths
  have ht' : (b 0 - a 0) * Real.cos t + (b 1 - a 1) * Real.sin t = 0 := by
    simpa [normalVector, frame, PiLp.inner_apply, mul_comm] using hortht
  have hprod : (b 0 - a 0) * Real.sin (s - t) = 0 := by
    rw [Real.sin_sub]
    linear_combination Real.sin s * ht' - Real.sin t * hs'
  have hz : Real.sin (s - t) = 0 :=
    (mul_eq_zero.mp hprod).resolve_left (sub_pos.mpr hab).ne'
  have := (Real.sin_eq_zero_iff_of_lt_of_lt
    (by linarith [hs.1, ht.2]) (by linarith [hs.2, ht.1])).mp hz
  linarith

/-- Grouping edge lengths by normal preserves the horizontal displacement identity. -/
lemma XMonotonePolylineData.sum_normal_lengths_mul_sin
    (p : XMonotonePolylineData) (D : Finset ℝ)
    (hD : ∀ t ∈ D, t ∈ Set.Ioo 0 Real.pi)
    (hlabels : ∀ i : Fin p.edges, ∃ t ∈ D,
      inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
        (normalVector (t : Real.Angle)) = 0) :
    ∑ t ∈ D, (∑ i : Fin p.edges,
      if inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
        (normalVector (t : Real.Angle)) = 0 then
        dist (p.vertices i.castSucc) (p.vertices i.succ) else 0) * Real.sin t =
      p.vertices (Fin.last p.edges) 0 - p.vertices 0 0 := by
  classical
  choose t ht horth using hlabels
  calc
    _ = ∑ i : Fin p.edges, ∑ u ∈ D,
        (if inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
          (normalVector (u : Real.Angle)) = 0 then
          dist (p.vertices i.castSucc) (p.vertices i.succ) else 0) * Real.sin u := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
    _ = ∑ i : Fin p.edges,
        dist (p.vertices i.castSucc) (p.vertices i.succ) * Real.sin (t i) := by
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
    _ = _ := p.sum_dist_mul_sin t (fun i ↦ hD _ (ht i)) horth

end MovingSofa
