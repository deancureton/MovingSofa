import MovingSofa.Analysis.SurfaceMeasure.WeakConvergence
import MovingSofa.Analysis.SurfaceMeasure.Properties

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace MovingSofa

/-- An upper bound by a moving surface atom passes to a Hausdorff limit. -/
theorem le_surfaceAreaMeasure_atom_of_tendsto {K : ℕ → ConvexBody Point}
    {L : ConvexBody Point}
    (hK : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point) (L : Set Point))
      atTop (𝓝 0)) {u : Real.Angle} {x : ℕ → ℝ} {a : ℝ}
    (hx : Tendsto x atTop (𝓝 a))
    (hle : ∀ n, x n ≤ (surfaceAreaMeasure (K n) {u}).toReal) :
    a ≤ (surfaceAreaMeasure L {u}).toReal := by
  let μs : ℕ → FiniteMeasure Real.Angle := fun n ↦
    ⟨surfaceAreaMeasure (K n), (surfaceAreaMeasure_face_union (K n)).1⟩
  let μ : FiniteMeasure Real.Angle :=
    ⟨surfaceAreaMeasure L, (surfaceAreaMeasure_face_union L).1⟩
  have hμ : Tendsto μs atTop (𝓝 μ) := by
    apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
    intro f
    exact surfaceAreaMeasure_weak_continuity K L hK f f.continuous
  have hclosed :
      Filter.limsup (fun n ↦ surfaceAreaMeasure (K n) {u}) atTop ≤
        surfaceAreaMeasure L {u} := by
    have h := FiniteMeasure.limsup_measure_closed_le_of_tendsto hμ
      (isClosed_singleton : IsClosed {u})
    change Filter.limsup (fun n ↦ surfaceAreaMeasure (K n) {u}) atTop ≤
      surfaceAreaMeasure L {u} at h
    exact h
  have hpoint : ∀ n, ENNReal.ofReal (x n) ≤ surfaceAreaMeasure (K n) {u} := by
    intro n
    exact ENNReal.ofReal_le_of_le_toReal (hle n)
  have hlimsup :
      Filter.limsup (fun n ↦ ENNReal.ofReal (x n)) atTop ≤
        Filter.limsup (fun n ↦ surfaceAreaMeasure (K n) {u}) atTop :=
    Filter.limsup_le_limsup (Eventually.of_forall hpoint)
  have hmain : ENNReal.ofReal a ≤ surfaceAreaMeasure L {u} := by
    calc
      ENNReal.ofReal a = Filter.limsup (fun n ↦ ENNReal.ofReal (x n)) atTop :=
        (ENNReal.tendsto_ofReal hx).limsup_eq.symm
      _ ≤ Filter.limsup (fun n ↦ surfaceAreaMeasure (K n) {u}) atTop := hlimsup
      _ ≤ surfaceAreaMeasure L {u} := hclosed
  let _ : IsFiniteMeasure (surfaceAreaMeasure L) := (surfaceAreaMeasure_face_union L).1
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp hmain

end MovingSofa
