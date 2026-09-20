import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Portmanteau for finite measures: the open-set inequality

Mathlib proves the open-set portmanteau inequality
`MeasureTheory.ProbabilityMeasure.le_liminf_measure_open_of_tendsto` for probability measures and
only the closed-set inequality `MeasureTheory.FiniteMeasure.limsup_measure_closed_le_of_tendsto`
for finite measures. This file supplies the missing open-set inequality for finite measures, by
combining the closed-set inequality on the complement with the convergence of the total masses.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace MeasureTheory.FiniteMeasure

/-- Portmanteau for finite measures: weak convergence bounds the mass of an open set by the
lower limit of the approximating masses. -/
theorem le_liminf_measure_open_of_tendsto
    {Ω ι : Type*} {L : Filter ι} [L.NeBot]
    [MeasurableSpace Ω] [TopologicalSpace Ω] [HasOuterApproxClosed Ω]
    [OpensMeasurableSpace Ω] {μ : FiniteMeasure Ω} {μs : ι → FiniteMeasure Ω}
    (hlim : Tendsto μs L (𝓝 μ)) {G : Set Ω} (hG : IsOpen G) :
    (μ : Measure Ω) G ≤ L.liminf (fun i ↦ (μs i : Measure Ω) G) := by
  have hclosed := MeasureTheory.FiniteMeasure.limsup_measure_closed_le_of_tendsto hlim
    hG.isClosed_compl
  rw [le_liminf_iff (by isBoundedDefault) (by isBoundedDefault)]
  intro y hy
  have hμGtop : (μ : Measure Ω) G ≠ ⊤ := measure_ne_top _ _
  have hyTop : y ≠ ⊤ := ne_top_of_lt (hy.trans_le (le_top))
  have hyR : y.toReal < ((μ : Measure Ω) G).toReal :=
    (ENNReal.toReal_lt_toReal hyTop hμGtop).mpr hy
  let d : ℝ := (((μ : Measure Ω) G).toReal - y.toReal) / 3
  have hd : 0 < d := by
    dsimp [d]
    linarith
  have hmass : Tendsto (fun i ↦ ((μs i).mass : ℝ)) L (𝓝 (μ.mass : ℝ)) :=
    (NNReal.continuous_coe.tendsto μ.mass).comp
      (MeasureTheory.FiniteMeasure.continuous_mass.tendsto μ |>.comp hlim)
  have hevmass : ∀ᶠ i in L, (μ.mass : ℝ) - d < ((μs i).mass : ℝ) :=
    hmass.eventually_const_lt (sub_lt_self _ hd)
  let q : ENNReal := ENNReal.ofReal (((μ : Measure Ω) Gᶜ).toReal + d)
  have hqd : 0 ≤ ((μ : Measure Ω) Gᶜ).toReal + d := by
    have hcR : 0 ≤ ((μ : Measure Ω) Gᶜ).toReal := ENNReal.toReal_nonneg
    linarith
  have hcompq : (μ : Measure Ω) Gᶜ < q := by
    rw [← ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top]
    simp only [ENNReal.toReal_ofReal hqd]
    linarith
  have hlsq : L.limsup (fun i ↦ (μs i : Measure Ω) Gᶜ) < q :=
    hclosed.trans_lt hcompq
  have hevcomp : ∀ᶠ i in L, (μs i : Measure Ω) Gᶜ < q :=
    eventually_lt_of_limsup_lt hlsq
  filter_upwards [hevmass, hevcomp] with i him hic
  have hmassEq : ((μs i : Measure Ω) univ).toReal = ((μs i).mass : ℝ) := by
    simp [← MeasureTheory.FiniteMeasure.ennreal_mass]
  have hcompR : ((μs i : Measure Ω) Gᶜ).toReal <
      ((μ : Measure Ω) Gᶜ).toReal + d := by
    have h := (ENNReal.toReal_lt_toReal (measure_ne_top _ _)
      ENNReal.ofReal_ne_top).mpr hic
    simpa [q, ENNReal.toReal_ofReal hqd] using h
  have hsplit : ((μs i : Measure Ω) G).toReal =
      ((μs i).mass : ℝ) - ((μs i : Measure Ω) Gᶜ).toReal := by
    rw [show (μs i : Measure Ω) G = (μs i : Measure Ω) univ -
      (μs i : Measure Ω) Gᶜ by
        rw [measure_compl hG.measurableSet (measure_ne_top _ _),
          ENNReal.sub_sub_cancel (measure_ne_top _ _)
            (measure_mono (subset_univ G))]]
    rw [ENNReal.toReal_sub_of_le (measure_mono (subset_univ _))
      (measure_ne_top _ _), hmassEq]
  have hμsplit : ((μ : Measure Ω) G).toReal =
      (μ.mass : ℝ) - ((μ : Measure Ω) Gᶜ).toReal := by
    rw [show (μ : Measure Ω) G = (μ : Measure Ω) univ -
      (μ : Measure Ω) Gᶜ by
        rw [measure_compl hG.measurableSet (measure_ne_top _ _),
          ENNReal.sub_sub_cancel (measure_ne_top _ _)
            (measure_mono (subset_univ G))]]
    rw [ENNReal.toReal_sub_of_le (measure_mono (subset_univ _))
      (measure_ne_top _ _)]
    simp [← MeasureTheory.FiniteMeasure.ennreal_mass]
  apply (ENNReal.toReal_lt_toReal hyTop (measure_ne_top _ _)).mp
  rw [hsplit]
  dsimp [d] at him hcompR hd
  linarith [hyR, hμsplit]

end MeasureTheory.FiniteMeasure
