import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open MeasureTheory

namespace EuclideanSpace

theorem volume_preserving_finTwoCoordinates :
    MeasurePreserving (fun p : EuclideanSpace ℝ (Fin 2) ↦ (p 0, p 1)) volume volume := by
  exact (volume_preserving_finTwoArrow ℝ).comp
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2))

/-- The volume of a closed coordinate box of the Euclidean plane. -/
theorem volume_setOf_apply_mem_Icc (l r b t : ℝ) :
    volume {p : EuclideanSpace ℝ (Fin 2) | p 0 ∈ Set.Icc l r ∧ p 1 ∈ Set.Icc b t} =
      ENNReal.ofReal (r - l) * ENNReal.ofReal (t - b) := by
  have h := volume_preserving_finTwoCoordinates.measure_preimage
    ((measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet :
      NullMeasurableSet (Set.Icc l r ×ˢ Set.Icc b t) (volume : Measure (ℝ × ℝ)))
  calc
    volume {p : EuclideanSpace ℝ (Fin 2) | p 0 ∈ Set.Icc l r ∧ p 1 ∈ Set.Icc b t} =
        volume (Set.Icc l r ×ˢ Set.Icc b t) := by
      convert h using 1
      congr 1
    _ = _ := by rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]

/-- The coordinates of a point of the Euclidean plane, listed second coordinate first. -/
def finTwoCoordinatesSwap (p : EuclideanSpace ℝ (Fin 2)) : ℝ × ℝ :=
  (p 1, p 0)

/-- Reading the plane coordinates in the reversed order is measure preserving. -/
theorem volume_preserving_finTwoCoordinatesSwap :
    MeasurePreserving finTwoCoordinatesSwap volume
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
  have hswap : MeasurePreserving Prod.swap
      ((volume : Measure ℝ).prod (volume : Measure ℝ))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    Measure.measurePreserving_swap
  convert hswap.comp volume_preserving_finTwoCoordinates using 1
  funext p
  rfl

end EuclideanSpace
