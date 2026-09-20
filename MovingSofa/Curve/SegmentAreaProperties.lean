import MovingSofa.Curve.SegmentArea.Parametrization
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import MovingSofa.Curve.Reparametrization

noncomputable section

namespace MovingSofa

open MeasureTheory Set

theorem segmentArea_jordan_and_frame (p q : Point) :
    (∃ A : RectifiableOrientedArc,
      A.val.carrier = segment ℝ p q ∧ A.val.startPoint = p ∧ A.val.endPoint = q ∧
      jordanArcArea A = segmentArea p q) ∧
    (∀ (t : Real.Angle) (h d : ℝ), p ∈ normalLine t h → q ∈ normalLine t h →
      q - p = d • tangentVector t → segmentArea p q = h * d / 2) := by
  constructor
  · by_cases hpq : p = q
    · subst q
      let Γ : OrientedJordanArc :=
        { carrier := segment ℝ p p
          startPoint := p
          endPoint := p
          parametrizable := by
            refine ⟨0, 0, le_rfl, (constBVPath 0 0 p).val,
              (constBVPath 0 0 p).property.1, ?_, ?_, rfl, rfl⟩
            · intro s t _
              apply Subtype.ext
              exact le_antisymm (s.property.2.trans t.property.1)
                (t.property.2.trans s.property.1)
            · simp [constBVPath] }
      let z : ArcBVParametrization Γ :=
        { a := 0
          b := 0
          ordered := le_rfl
          path := constBVPath 0 0 p
          injective := by
            intro s t _
            apply Subtype.ext
            exact le_antisymm (s.property.2.trans t.property.1)
              (t.property.2.trans s.property.1)
          range_eq := by simp [constBVPath, Γ]
          start_eq := rfl
          end_eq := rfl }
      let A : RectifiableOrientedArc := ⟨Γ, ⟨z⟩⟩
      refine ⟨A, rfl, rfl, rfl, ?_⟩
      change curveAreaFunctional (Classical.choice A.property).path = segmentArea p p
      calc
        _ = curveAreaFunctional z.path :=
          (curveArea_reparametrization.2.1 Γ Γ
            (Classical.choice A.property) z rfl).1 rfl rfl
        _ = 0 := curveArea_reparametrization.2.2.2 0 0 z.path p (by intro t; rfl)
        _ = segmentArea p p := by simp [segmentArea, planeCrossProduct]; ring
    · let Γ : OrientedJordanArc :=
        { carrier := segment ℝ p q
          startPoint := p
          endPoint := q
          parametrizable := by
            refine ⟨0, 1, by norm_num, Path.segment p q,
              (Path.segment p q).continuous, Path.segment_injective_of_ne hpq,
              Path.range_segment p q, ?_, ?_⟩
            · simp
            · simp }
      let z : ArcBVParametrization Γ :=
        { a := 0
          b := 1
          ordered := by norm_num
          path := lineSegmentBVPath p q
          injective := Path.segment_injective_of_ne hpq
          range_eq := Path.range_segment p q
          start_eq := by simp [lineSegmentBVPath, Γ]
          end_eq := by simp [lineSegmentBVPath, Γ] }
      let A : RectifiableOrientedArc := ⟨Γ, ⟨z⟩⟩
      refine ⟨A, rfl, rfl, rfl, ?_⟩
      change curveAreaFunctional (Classical.choice A.property).path = segmentArea p q
      calc
        _ = curveAreaFunctional z.path :=
          (curveArea_reparametrization.2.1 Γ Γ
            (Classical.choice A.property) z rfl).1 rfl rfl
        _ = segmentArea p q := curveAreaFunctional_lineSegmentBVPath p q
  · intro t h d hp hq hd
    simp only [normalLine, Set.mem_ofPred_eq, segmentArea, planeCrossProduct] at hp hq ⊢
    have hd0 := congrArg (fun x : Point => x 0) hd
    have hd1 := congrArg (fun x : Point => x 1) hd
    simp [normalVector, tangentVector, frame] at hp hq hd0 hd1 ⊢
    rw [PiLp.inner_apply, Fin.sum_univ_two, Real.inner_apply, Real.inner_apply] at hp hq
    simp at hp hq
    have hq0 : q.ofLp 0 = p.ofLp 0 - d * t.sin := by linarith [hd0]
    have hq1 : q.ofLp 1 = p.ofLp 1 + d * t.cos := by linarith [hd1]
    rw [hq0, hq1]
    calc
      p.ofLp 0 * (p.ofLp 1 + d * t.cos) - p.ofLp 1 * (p.ofLp 0 - d * t.sin) =
          d * (p.ofLp 0 * t.cos + p.ofLp 1 * t.sin) := by ring
      _ = d * h := by rw [hp]
      _ = h * d := by ring

theorem segmentArea_collinear_origin (p q : Point)
    (h : Collinear ℝ ({0, p, q} : Set Point)) : segmentArea p q = 0 := by
  obtain ⟨v, hv⟩ := (collinear_iff_of_mem (by simp : (0 : Point) ∈ ({0, p, q} : Set Point))).mp h
  obtain ⟨a, ha⟩ := hv p (by simp)
  obtain ⟨b, hb⟩ := hv q (by simp)
  simp only [vadd_eq_add, add_zero] at ha hb
  rw [ha, hb]
  simp [segmentArea, planeCrossProduct]
  ring

end MovingSofa
