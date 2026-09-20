import MovingSofa.Curve.Jordan.Parametrization
import MovingSofa.Curve.Jordan.AreaTransport
import MovingSofa.Curve.Jordan.CyclicRotation

noncomputable section

namespace MovingSofa

/-- Same-carrier closed Jordan parametrizations have signed areas determined by orientation. -/
theorem curveArea_closed_same_carrier (Γ Δ : OrientedJordanCurve)
    (x : ClosedBVParametrization Γ) (y : ClosedBVParametrization Δ)
    (hcarrier : Γ.carrier = Δ.carrier) :
    (Γ.counterclockwise = Δ.counterclockwise →
      curveAreaFunctional x.path = curveAreaFunctional y.path) ∧
    (Γ.counterclockwise ≠ Δ.counterclockwise →
      curveAreaFunctional x.path = -curveAreaFunctional y.path) := by
  have hy : IsOrientedJordanParametrization y.ordered Γ.carrier Δ.counterclockwise y.path.val := by
    rw [hcarrier]
    exact y.oriented
  have hcompare (z : ClosedBVParametrization Γ)
      (hstart : z.path.val ⟨z.a, le_rfl, z.ordered⟩ =
        y.path.val ⟨y.a, le_rfl, y.ordered⟩) :
      (Γ.counterclockwise = Δ.counterclockwise →
        curveAreaFunctional z.path = curveAreaFunctional y.path) ∧
      (Γ.counterclockwise ≠ Δ.counterclockwise →
        curveAreaFunctional z.path = -curveAreaFunctional y.path) := by
    obtain ⟨φ, hφc, hφs, hφo, hcomp⟩ :=
      z.exists_reparametrization_of_start_eq y hcarrier hstart
    exact curveArea_eq_of_oriented_reparametrization z.ordered y.ordered z.path y.path
      z.oriented hy φ hφc hφs hφo hcomp
  by_cases hstart : x.path.val ⟨x.a, le_rfl, x.ordered⟩ =
      y.path.val ⟨y.a, le_rfl, y.ordered⟩
  · exact hcompare x hstart
  have hmem : y.path.val ⟨y.a, le_rfl, y.ordered⟩ ∈ Set.range x.path.val := by
    rw [x.oriented.2.2.2.1, hcarrier, ← y.oriented.2.2.2.1]
    exact Set.mem_range_self _
  obtain ⟨s, hsb, hs⟩ := exists_param_lt_top_of_mem_range x.oriented.1 x.path.val
    x.oriented.2.2.2.2.1 hmem
  have has : x.a < (s : ℝ) := by
    apply lt_of_le_of_ne s.property.1
    intro heq
    have hsa : s = ⟨x.a, le_rfl, x.ordered⟩ := Subtype.ext heq.symm
    apply hstart
    simpa only [hsa] using hs
  obtain ⟨r, hr, hrstart, hrarea⟩ :=
    exists_oriented_cyclic_rotation x.ordered x.path x.oriented s has hsb
  let z : ClosedBVParametrization Γ :=
    { a := 0, b := 2, ordered := by norm_num, path := r, oriented := hr }
  have hzstart : z.path.val ⟨z.a, le_rfl, z.ordered⟩ =
      y.path.val ⟨y.a, le_rfl, y.ordered⟩ := hrstart.trans hs
  simpa only [show z.path = r from rfl, hrarea] using hcompare z hzstart

end MovingSofa
