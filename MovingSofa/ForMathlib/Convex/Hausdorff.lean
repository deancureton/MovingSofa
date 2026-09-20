import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.MetricSpace.Closeds
import Mathlib.Topology.Sequences

open Filter TopologicalSpace
open scoped Topology

/-- Hausdorff limits of nonempty compact convex sets are convex. -/
theorem TopologicalSpace.NonemptyCompacts.convex_of_tendsto {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {l : Filter ι} [l.NeBot] {K : ι → NonemptyCompacts E} {L : NonemptyCompacts E}
    (hK : ∀ n, Convex ℝ (K n : Set E)) (hlim : Tendsto K l (𝓝 L)) :
    Convex ℝ (L : Set E) := by
  have happrox : ∀ x ∈ (L : Set E), ∃ p : ι → E,
      (∀ n, p n ∈ (K n : Set E)) ∧ Tendsto p l (𝓝 x) := by
    intro x hx
    choose p hp hd using fun n ↦ (K n).isCompact.exists_infDist_eq_dist (K n).nonempty x
    refine ⟨p, hp, ?_⟩
    have hinf := (NonemptyCompacts.lipschitz_infDist_const x).continuous.tendsto L |>.comp hlim
    have hz : Metric.infDist x (L : Set E) = 0 := Metric.infDist_zero_of_mem hx
    rw [hz] at hinf
    change Tendsto (fun n ↦ Metric.infDist x (K n : Set E)) l (𝓝 0) at hinf
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [Function.comp_apply, hd, dist_comm] using hinf
  intro x hx y hy a b ha hb hab
  obtain ⟨p, hp, hpx⟩ := happrox x hx
  obtain ⟨q, hq, hqy⟩ := happrox y hy
  have hz := (hpx.const_smul a).add (hqy.const_smul b)
  have hi := NonemptyCompacts.uniformContinuous_infDist.continuous.tendsto
    (a • x + b • y, L) |>.comp (hz.prodMk_nhds hlim)
  have hzero : (fun n ↦ Metric.infDist (a • p n + b • q n) (K n : Set E)) = fun _ ↦ 0 := by
    funext n
    exact Metric.infDist_zero_of_mem (hK n (hp n) (hq n) ha hb hab)
  change Tendsto (fun n ↦ Metric.infDist (a • p n + b • q n) (K n : Set E))
    l (𝓝 (Metric.infDist (a • x + b • y) (L : Set E))) at hi
  rw [hzero] at hi
  exact (L.isCompact.isClosed.mem_iff_infDist_zero L.nonempty).mpr
    (tendsto_nhds_unique hi tendsto_const_nhds)
