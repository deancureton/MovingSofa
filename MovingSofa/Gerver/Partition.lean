import MovingSofa.Gerver.Parameters

noncomputable section

namespace MovingSofa

/-- The ten half-open Gerver phase intervals, indexed from zero. -/
def gerverPhaseIntervals (j : Fin 10) : Set ℝ :=
  let lower (i : Fin 5) := Set.Ico (gerverStageTimes i.castSucc) (gerverStageTimes i.succ)
  Fin.addCases (motive := fun _ ↦ Set ℝ) lower
    (fun i ↦ (fun t ↦ Real.pi - t) '' lower i.rev) j

/-- The ten Gerver phase intervals, written out as explicit half-open real intervals. -/
theorem gerverPhaseIntervals_explicit (j : Fin 10) :
    gerverPhaseIntervals j =
      ![Set.Ico 0 GerversSofa.φ,
        Set.Ico GerversSofa.φ GerversSofa.θ,
        Set.Ico GerversSofa.θ (Real.pi / 2 - GerversSofa.θ),
        Set.Ico (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2 - GerversSofa.φ),
        Set.Ico (Real.pi / 2 - GerversSofa.φ) (Real.pi / 2),
        Set.Ioc (Real.pi / 2) (Real.pi / 2 + GerversSofa.φ),
        Set.Ioc (Real.pi / 2 + GerversSofa.φ) (Real.pi / 2 + GerversSofa.θ),
        Set.Ioc (Real.pi / 2 + GerversSofa.θ) (Real.pi - GerversSofa.θ),
        Set.Ioc (Real.pi - GerversSofa.θ) (Real.pi - GerversSofa.φ),
        Set.Ioc (Real.pi - GerversSofa.φ) Real.pi] j := by
  fin_cases j
  all_goals simp [gerverPhaseIntervals, gerverStageTimes, Fin.addCases, Fin.rev]
  all_goals congr 1 <;> ring

end MovingSofa
