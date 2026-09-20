import MovingSofa.Curve.AreaTransport
import MovingSofa.Curve.Jordan.Area

noncomputable section

namespace MovingSofa

open MeasureTheory Set

/-- Same-carrier Jordan arcs have equal or opposite signed areas according to their endpoints. -/
theorem curveArea_arc_same_carrier
    (Γ Δ : OrientedJordanArc) (x : ArcBVParametrization Γ)
    (y : ArcBVParametrization Δ) (hcarrier : Γ.carrier = Δ.carrier) :
    (Γ.startPoint = Δ.startPoint → Γ.endPoint = Δ.endPoint →
      curveAreaFunctional x.path = curveAreaFunctional y.path) ∧
    (Γ.startPoint = Δ.endPoint → Γ.endPoint = Δ.startPoint →
      curveAreaFunctional x.path = -curveAreaFunctional y.path) := by
  let _ : Fact (x.a ≤ x.b) := ⟨x.ordered⟩
  let _ : Fact (y.a ≤ y.b) := ⟨y.ordered⟩
  have hxemb : Topology.IsEmbedding x.path.val :=
    (x.path.property.1.isClosedEmbedding x.injective).isEmbedding
  let φ : Set.Icc y.a y.b → Set.Icc x.a x.b := fun t ↦
    hxemb.toHomeomorph.symm ⟨y.path.val t, by
      rw [x.range_eq, hcarrier, ← y.range_eq]
      exact Set.mem_range_self t⟩
  have hφc : Continuous φ :=
    hxemb.toHomeomorph.symm.continuous.comp <|
      y.path.property.1.subtype_mk _
  have hxy (t : Set.Icc y.a y.b) : x.path.val (φ t) = y.path.val t := by
    exact congrArg Subtype.val (hxemb.toHomeomorph.apply_symm_apply
      ⟨y.path.val t, by
        rw [x.range_eq, hcarrier, ← y.range_eq]
        exact Set.mem_range_self t⟩)
  have hφi : Function.Injective φ := fun s t hst ↦
    y.injective <| by rw [← hxy s, ← hxy t, hst]
  have hφs : Function.Surjective φ := by
    intro s
    have hmem : x.path.val s ∈ Set.range y.path.val := by
      rw [y.range_eq, ← hcarrier, ← x.range_eq]
      exact Set.mem_range_self s
    obtain ⟨t, ht⟩ := hmem
    refine ⟨t, ?_⟩
    apply x.injective
    rw [hxy t, ht]
  have hxbot : x.path.val (⊥ : Set.Icc x.a x.b) = Γ.startPoint := by
    convert x.start_eq using 1
  have hxtop : x.path.val (⊤ : Set.Icc x.a x.b) = Γ.endPoint := by
    convert x.end_eq using 1
  have hybot : y.path.val (⊥ : Set.Icc y.a y.b) = Δ.startPoint := by
    convert y.start_eq using 1
  have hytop : y.path.val (⊤ : Set.Icc y.a y.b) = Δ.endPoint := by
    convert y.end_eq using 1
  have hmono (hstart : Γ.startPoint = Δ.startPoint)
      (hend : Γ.endPoint = Δ.endPoint) : Monotone φ := by
    apply (hφc.strictMono_of_inj_boundedOrder ?_ hφi).monotone
    have hbot : φ ⊥ = ⊥ := by
      apply x.injective
      rw [hxy ⊥, hybot, ← hstart, hxbot]
    have htop : φ ⊤ = ⊤ := by
      apply x.injective
      rw [hxy ⊤, hytop, ← hend, hxtop]
    rw [hbot, htop]
    exact bot_le
  have hanti (hstart : Γ.startPoint = Δ.endPoint)
      (hend : Γ.endPoint = Δ.startPoint) : Antitone φ := by
    apply (hφc.strictAnti_of_inj_boundedOrder ?_ hφi).antitone
    have htop : φ ⊤ = ⊥ := by
      apply x.injective
      rw [hxy ⊤, hytop, ← hstart, hxbot]
    have hbot : φ ⊥ = ⊤ := by
      apply x.injective
      rw [hxy ⊥, hybot, ← hend, hxtop]
    rw [htop, hbot]
    exact bot_le
  constructor
  · intro hstart hend
    obtain ⟨z, hz, hzarea⟩ := curveArea_comp_monotone_surjective
      x.ordered y.ordered x.path φ hφc (hmono hstart hend) hφs
    have hzy : z = y.path := by
      apply Subtype.ext
      rw [hz]
      funext t
      exact hxy t
    simpa [hzy] using hzarea.symm
  · intro hstart hend
    obtain ⟨z, hz, hzarea⟩ := curveArea_comp_antitone_surjective
      x.ordered y.ordered x.path φ hφc (hanti hstart hend) hφs
    have hzy : z = y.path := by
      apply Subtype.ext
      rw [hz]
      funext t
      exact hxy t
    rw [hzy] at hzarea
    linarith

end MovingSofa
