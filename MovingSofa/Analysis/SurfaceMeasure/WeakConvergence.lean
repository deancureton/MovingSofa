import MovingSofa.Analysis.SurfaceMeasure.GraphConvergence

noncomputable section

open scoped BigOperators
open Filter MeasureTheory
open scoped Topology

namespace MovingSofa

private def normalCoordinateFrames : Fin 4 → Point ≃ₗᵢ[ℝ] Point :=
  ![LinearIsometryEquiv.refl ℝ Point, LinearIsometryEquiv.neg ℝ,
    coordinateSwap, coordinateSwap.trans (LinearIsometryEquiv.neg ℝ)]

private theorem exists_normalCoordinateFrame (t : Real.Angle) :
    ∃ i, (1 / 2 : ℝ) < normalCoordinateFrames i (normalVector t) 1 := by
  by_contra h
  push Not at h
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  simp [normalCoordinateFrames, coordinateSwap, normalVector, frame] at h0 h1 h2 h3
  have hs : t.sin ^ 2 ≤ 1 / 4 := by nlinarith
  have hc : t.cos ^ 2 ≤ 1 / 4 := by nlinarith
  nlinarith [t.cos_sq_add_sin_sq]

/-- Four coordinate half-circles admit a continuous partition of unity supported
where the upward component of the normal is at least one half. -/
theorem exists_normalCoordinate_partition :
    ∃ (e : Fin 4 → Point ≃ₗᵢ[ℝ] Point) (χ : Fin 4 → Real.Angle → ℝ),
      (∀ i, Continuous (χ i)) ∧ (∀ t, ∑ i, χ i t = 1) ∧
        (∀ i t, e i (normalVector t) 1 < 1 / 2 → χ i t = 0) := by
  let ρ : Fin 4 → Real.Angle → ℝ := fun i t ↦
    max 0 (normalCoordinateFrames i (normalVector t) 1 - 1 / 2)
  have hρ : ∀ i, Continuous (ρ i) := by
    intro i
    dsimp [ρ]
    exact continuous_const.max
      (((PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 1).comp
        ((normalCoordinateFrames i).continuous.comp continuous_normalVector_angle)).sub continuous_const)
  have hpos (t : Real.Angle) : 0 < ∑ i, ρ i t := by
    obtain ⟨i, hi⟩ := exists_normalCoordinateFrame t
    apply Finset.sum_pos' (fun j _ ↦ le_max_left _ _)
    refine ⟨i, Finset.mem_univ _, ?_⟩
    exact (sub_pos.mpr hi).trans_le (le_max_right _ _)
  refine ⟨normalCoordinateFrames, fun i t ↦ ρ i t / ∑ j, ρ j t, ?_, ?_, ?_⟩
  · intro i
    exact (hρ i).div (continuous_finsetSum _ fun j _ ↦ hρ j)
      (fun t ↦ (hpos t).ne')
  · intro t
    rw [← Finset.sum_div]
    exact div_self (hpos t).ne'
  · intro i t ht
    have hz : ρ i t = 0 := max_eq_left (sub_nonpos.mpr ht.le)
    dsimp only
    rw [hz, zero_div]

/-- Convergence for test functions supported in upward normal patches implies
convergence for all continuous test functions. -/
theorem tendsto_surfaceIntegral_of_normal_patches
    (K : ℕ → ConvexBody Point) (L : ConvexBody Point)
    (hpatch : ∀ (e : Point ≃ₗᵢ[ℝ] Point) (ψ : Real.Angle → ℝ), Continuous ψ →
      (∀ t, e (normalVector t) 1 < 1 / 2 → ψ t = 0) →
      Tendsto (fun n ↦ ∫ t, ψ t ∂surfaceAreaMeasure (K n)) atTop
        (𝓝 (∫ t, ψ t ∂surfaceAreaMeasure L)))
    (φ : Real.Angle → ℝ) (hφ : Continuous φ) :
    Tendsto (fun n ↦ ∫ t, φ t ∂surfaceAreaMeasure (K n)) atTop
      (𝓝 (∫ t, φ t ∂surfaceAreaMeasure L)) := by
  obtain ⟨e, χ, hχ, hsum, hsupp⟩ := exists_normalCoordinate_partition
  let ψ : Fin 4 → Real.Angle → ℝ := fun i t ↦ φ t * χ i t
  have hψ (i : Fin 4) : Continuous (ψ i) := hφ.mul (hχ i)
  have hψsum (t : Real.Angle) : ∑ i, ψ i t = φ t := by
    simp only [ψ, ← Finset.mul_sum, hsum, mul_one]
  have hint (C : ConvexBody Point) :
      ∑ i, (∫ t, ψ i t ∂surfaceAreaMeasure C) = ∫ t, φ t ∂surfaceAreaMeasure C := by
    let _ := (surfaceAreaMeasure_construction C).1
    rw [← integral_finsetSum]
    · simp only [hψsum]
    · intro i _
      exact integrableOn_univ.mp ((hψ i).continuousOn.integrableOn_compact isCompact_univ)
  have ht (i : Fin 4) := hpatch (e i) (ψ i) (hψ i) (by
    intro t ht
    simp only [ψ, hsupp i t ht, mul_zero])
  have h := tendsto_finsetSum Finset.univ (fun i _ ↦ ht i)
  simpa only [hint] using h

theorem surfaceAreaMeasure_weak_continuity (K : ℕ → ConvexBody Point)
    (L : ConvexBody Point)
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point) (L : Set Point))
      atTop (𝓝 0)) (φ : Real.Angle → ℝ) (hφ : Continuous φ) :
    Tendsto (fun n ↦ ∫ u, φ u ∂surfaceAreaMeasure (K n))
      atTop (𝓝 (∫ u, φ u ∂surfaceAreaMeasure L)) := by
  apply tendsto_surfaceIntegral_of_normal_patches K L _ φ hφ
  intro e ψ hψ hsupp
  exact tendsto_integral_surfaceAreaMeasure_of_hausdorffDist K L hlim 0 e hψ
    (by norm_num : (0 : ℝ) < 1 / 2) hsupp

end MovingSofa
