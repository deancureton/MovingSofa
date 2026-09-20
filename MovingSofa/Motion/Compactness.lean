import MovingSofa.Motion.Basic
import Mathlib.Topology.Connected.TotallyDisconnected

noncomputable section

open Set MeasureTheory
open scoped unitInterval

namespace MovingSofa

private theorem abs_le_of_affine_coordinate {a b c x y z : ℝ}
    (ha : a ≠ 0) (hy : |y| ≤ 1) (hz : |z| ≤ 1) (heq : z = a * x + b * y + c) :
    |x| ≤ (1 + |b| + |c|) / |a| := by
  have hmul : |a| * |x| ≤ 1 + |b| + |c| := by
    calc
      |a| * |x| = |z - (b * y + c)| := by rw [← abs_mul]; congr 1; linarith
      _ ≤ |z| + |b * y + c| := abs_sub _ _
      _ ≤ 1 + (|b| * |y| + |c|) := by
        grw [hz, abs_add_le, abs_mul]
      _ ≤ 1 + |b| + |c| := by nlinarith [abs_nonneg b]
  exact (le_div_iff₀ (abs_pos.mpr ha)).mpr (by nlinarith)

private theorem norm_le_of_coordinate_bounds {p : Point} {C : ℝ}
    (hC : 0 ≤ C) (hx : |p 0| ≤ C) (hy : |p 1| ≤ 1) : ‖p‖ ≤ C + 1 := by
  have hn : ‖p‖ ^ 2 = (p 0) ^ 2 + (p 1) ^ 2 := by
    simpa [Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq p
  have hx2 := sq_le_sq₀ (abs_nonneg (p 0)) hC |>.mpr hx
  have hy2 := sq_le_sq₀ (abs_nonneg (p 1)) (by positivity : (0 : ℝ) ≤ 1) |>.mpr hy
  rw [sq_abs] at hx2 hy2
  nlinarith [norm_nonneg p]

private theorem affineIsometry_coordinate (e : Point ≃ᵃⁱ[ℝ] Point) (p : Point) (i : Fin 2) :
    e p i = (e.linearIsometryEquiv !₂[1, 0]) i * p 0 +
      (e.linearIsometryEquiv !₂[0, 1]) i * p 1 + e 0 i := by
  have hp : p = p 0 • !₂[1, 0] + p 1 • !₂[0, 1] := by
    ext j
    fin_cases j <;> simp
  have he := e.map_vadd (0 : Point) p
  change e (p + 0) = e.linearIsometryEquiv p + e 0 at he
  rw [add_zero] at he
  rw [he, hp, map_add, map_smul, map_smul]
  simp [mul_comm]

private theorem isBounded_affine_strip (e : Point ≃ᵃⁱ[ℝ] Point) (i : Fin 2)
    (hi : (e.linearIsometryEquiv !₂[1, 0]) i ≠ 0) :
    Bornology.IsBounded {p : Point | |p 1| ≤ 1 ∧ |e p i| ≤ 1} := by
  let C := (1 + |(e.linearIsometryEquiv !₂[0, 1]) i| + |e 0 i|) /
    |(e.linearIsometryEquiv !₂[1, 0]) i|
  have hC : 0 ≤ C := by dsimp [C]; positivity
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨C + 1, fun p hp ↦ ?_⟩
  apply norm_le_of_coordinate_bounds hC _ hp.1
  exact abs_le_of_affine_coordinate hi hp.1 hp.2 (affineIsometry_coordinate e p i)

private theorem abs_snd_le_one_of_mem_horizontal {p : Point}
    (hp : p ∈ horizontalHallway) : |p 1| ≤ 1 := by
  obtain ⟨x, y, hxy, rfl⟩ := hp
  simpa using
    (abs_le.mpr ⟨by linarith [hxy.2.1], hxy.2.2⟩ : |y| ≤ 1)

private theorem abs_fst_le_one_of_mem_vertical {p : Point}
    (hp : p ∈ verticalHallway) : |p 0| ≤ 1 := by
  obtain ⟨x, y, hxy, rfl⟩ := hp
  simpa using
    (abs_le.mpr ⟨by linarith [hxy.1], hxy.2.1⟩ : |x| ≤ 1)

private theorem isBounded_of_mixed_direction (s : Set Point)
    (m : I → Point ≃ᵃⁱ[ℝ] Point) (h : IsMovingSofa s m) (t : I)
    (h0 : ((m t).linearIsometryEquiv !₂[1, 0]) 0 ≠ 0)
    (h1 : ((m t).linearIsometryEquiv !₂[1, 0]) 1 ≠ 0) : Bornology.IsBounded s := by
  apply ((isBounded_affine_strip (m t) 0 h0).union
    (isBounded_affine_strip (m t) 1 h1)).subset
  intro p hp
  have hy := abs_snd_le_one_of_mem_horizontal (h.initial hp)
  rcases h.subset_hallway t ⟨p, hp, rfl⟩ with hhor | hvert
  · exact Or.inr ⟨hy, abs_snd_le_one_of_mem_horizontal hhor⟩
  · exact Or.inl ⟨hy, abs_fst_le_one_of_mem_vertical hvert⟩

/-- A set admitting a canonical hallway motion is bounded. -/
theorem IsMovingSofa.isBounded {s : Set Point}
    {m : I → Point ≃ᵃⁱ[ℝ] Point} (h : IsMovingSofa s m) : Bornology.IsBounded s := by
  let d : I → Point := fun t ↦ (m t).linearIsometryEquiv !₂[1, 0]
  have hd : Continuous d := by
    have he (t : I) : d t = m t !₂[1, 0] - m t 0 := by
      have he := (m t).map_vadd (0 : Point) !₂[1, 0]
      change m t (!₂[1, 0] + 0) = d t + m t 0 at he
      rw [add_zero] at he
      exact eq_sub_iff_add_eq.mpr he.symm
    simp_rw [show d = (fun t ↦ m t !₂[1, 0] - m t 0) from funext he]
    have hm : Continuous (fun t ↦ (m t).toAffineIsometry.toContinuousAffineMap) :=
      continuous_induced_dom.comp h.continuous
    exact (hm.eval_const _).sub (hm.eval_const _)
  have hnorm (t : I) : (d t 0) ^ 2 + (d t 1) ^ 2 = 1 := by
    have hn : ‖d t‖ = 1 := by
      dsimp [d]
      rw [(m t).linearIsometryEquiv.norm_map]
      simp [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    have hs := EuclideanSpace.real_norm_sq_eq (d t)
    simpa [hn, Fin.sum_univ_two] using hs.symm
  by_cases hmix : ∃ t, d t 0 ≠ 0 ∧ d t 1 ≠ 0
  · obtain ⟨t, h0, h1⟩ := hmix
    exact isBounded_of_mixed_direction s m h t h0 h1
  have hmem (t : I) : d t 0 ∈ ({-1, 0, 1} : Set ℝ) := by
    by_cases h0 : d t 0 = 0
    · simp [h0]
    have h1 : d t 1 = 0 := by
      by_contra hn
      exact hmix ⟨t, h0, hn⟩
    have hs : (d t 0) ^ 2 = (1 : ℝ) ^ 2 := by simpa [h1] using hnorm t
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hs) with he | he <;> simp [he]
  have hc : Continuous (fun t ↦ d t 0) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) 0).continuous.comp hd
  have hconst (t : I) : d t 0 = d 0 0 :=
    isPreconnected_univ.constant_of_mapsTo
      (((finite_singleton (1 : ℝ)).insert 0).insert (-1)).isDiscrete
      hc.continuousOn (fun t _ ↦ hmem t) (mem_univ t) (mem_univ 0)
  have hd0 : d 0 0 = 1 := by simp only [d, h.zero]; rfl
  have hdir : ((m 1).linearIsometryEquiv !₂[1, 0]) 0 ≠ 0 := by
    change d 1 0 ≠ 0
    rw [hconst, hd0]
    norm_num
  apply (isBounded_affine_strip (m 1) 0 hdir).subset
  intro p hp
  exact ⟨abs_snd_le_one_of_mem_horizontal (h.initial hp),
    abs_fst_le_one_of_mem_vertical (h.final ⟨p, hp, rfl⟩)⟩

end MovingSofa
