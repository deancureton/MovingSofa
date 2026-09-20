import MovingSofa.Analysis.Stieltjes.Calculus
import MovingSofa.Analysis.Stieltjes.Linearity

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace MovingSofa

/-- Componentwise product rule for the Euclidean pairing of two planar interval-BV functions,
when the second function is continuous. -/
theorem intervalStieltjes_inner_fin_two {a b : ℝ} (hab : a ≤ b)
    (f g : Fin 2 → RightContinuousIntervalBV a b)
    (hg : ∀ i, Continuous (g i).toFun) :
    ∃ h : RightContinuousIntervalBV a b,
      (∀ t, h.toFun t = ∑ i, (f i).toFun t * (g i).toFun t) ∧
      ∀ E : Set (Icc a b), MeasurableSet E →
        intervalStieltjesMeasure h E =
          ∑ i, (intervalStieltjesIntegral (f i) (g i).toFun E +
            intervalStieltjesIntegral (g i) (f i).toFun E) := by
  obtain ⟨p0, hp0, hp0m⟩ := intervalStieltjes_product a b hab (f 0) (g 0) (Or.inr (hg 0))
  obtain ⟨p1, hp1, hp1m⟩ := intervalStieltjes_product a b hab (f 1) (g 1) (Or.inr (hg 1))
  obtain ⟨h, hh, hhm⟩ := intervalStieltjes_linear_combination a b hab p0 p1 1 1
  refine ⟨h, ?_, ?_⟩
  · intro t
    rw [hh, hp0, hp1, Fin.sum_univ_two]
    ring
  · intro E hE
    rw [show intervalStieltjesMeasure h E =
        intervalStieltjesMeasure p0 E + intervalStieltjesMeasure p1 E by
      rw [hhm]
      simp]
    rw [hp0m E hE, hp1m E hE, Fin.sum_univ_two]

end MovingSofa
