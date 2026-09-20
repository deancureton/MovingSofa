import MovingSofa.Convex.CombinationProperties
import MovingSofa.Analysis.SurfaceMeasure.Boundary
import MovingSofa.Analysis.Stieltjes.Continuous

noncomputable section

open MeasureTheory
open scoped unitInterval

namespace MovingSofa

private theorem intervalStieltjesMeasure_congr {a b : ℝ}
    (f g : RightContinuousIntervalBV a b) (h : ∀ x, f.toFun x = g.toFun x) :
    intervalStieltjesMeasure f = intervalStieltjesMeasure g := by
  have hfun : f.toFun = g.toFun := funext h
  cases f with
  | mk ff hfb hfr =>
    cases g with
    | mk gf hgb hgr =>
      simp only at hfun ⊢
      subst gf
      rfl

/-- Planar surface area measures commute with convex combinations. -/
theorem surfaceAreaMeasure_convexBodyCombination (t : I)
    (K L : ConvexBody Point) :
    surfaceAreaMeasure (convexBodyCombination t K L) =
      ENNReal.ofReal (1 - (t : ℝ)) • surfaceAreaMeasure K +
        ENNReal.ofReal (t : ℝ) • surfaceAreaMeasure L := by
  let r : ℝ := 1 - (t : ℝ)
  let s : ℝ := t
  let M := convexBodyCombination t K L
  have hvertex (u : Real.Angle) :
      (edgeVertices M u).1 = r • (edgeVertices K u).1 + s • (edgeVertices L u).1 :=
    (edgeVertices_convexBodyCombination t K L u).1
  have hab : (0 : ℝ) < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hturn : 2 * Real.pi ≤ (0 : ℝ) + 2 * Real.pi := by simp
  obtain ⟨fM, hfM, hmM⟩ := positiveVertex_stieltjes_surface M 0 (2 * Real.pi) hab hturn
  obtain ⟨fK, hfK, hmK⟩ := positiveVertex_stieltjes_surface K 0 (2 * Real.pi) hab hturn
  obtain ⟨fL, hfL, hmL⟩ := positiveVertex_stieltjes_surface L 0 (2 * Real.pi) hab hturn
  have hmeasure (i : Fin 2) : intervalStieltjesMeasure (fM i) =
      r • intervalStieltjesMeasure (fK i) + s • intervalStieltjesMeasure (fL i) := by
    obtain ⟨f, hfun, hfm⟩ := intervalStieltjes_linear_combination
      0 (2 * Real.pi) hab.le (fK i) (fL i) r s
    have heq : intervalStieltjesMeasure f = intervalStieltjesMeasure (fM i) := by
      apply intervalStieltjesMeasure_congr
      intro x
      rw [hfun, hfK, hfL, hfM]
      have hv := congrArg (fun p : Point ↦ p i)
        (hvertex (((x : Set.Icc (0 : ℝ) (2 * Real.pi)) : ℝ) : Real.Angle))
      simpa [r, s] using hv.symm
    rwa [← heq]
  ext A hA
  let E : Set (Set.Icc (0 : ℝ) (2 * Real.pi)) :=
    {x | 0 < (x : ℝ) ∧ (((x : ℝ) : Real.Angle)) ∈ A}
  have hE : MeasurableSet E := by
    exact (measurableSet_Ioi.preimage measurable_subtype_coe).inter
      (hA.preimage (Real.Angle.continuous_coe.comp continuous_subtype_val).measurable)
  have hEa : ∀ x ∈ E, 0 < (x : ℝ) := fun _ hx ↦ hx.1
  have himage : (fun x : Set.Icc (0 : ℝ) (2 * Real.pi) ↦
      (((x : ℝ) : Real.Angle))) '' E = A := by
    ext u
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx.2
    · intro hu
      let _ : Fact (0 < 2 * Real.pi) := ⟨hab⟩
      let x := AddCircle.equivIoc (2 * Real.pi) 0 u
      have hx : (x : ℝ) ∈ Set.Ioc (0 : ℝ) (2 * Real.pi) := by simpa using x.property
      let y : Set.Icc (0 : ℝ) (2 * Real.pi) := ⟨x, hx.1.le, hx.2⟩
      have hxu : (((x : ℝ) : Real.Angle)) = u := AddCircle.coe_equivIoc
      refine ⟨y, ⟨hx.1, ?_⟩, ?_⟩
      · simpa [y, hxu] using hu
      · simpa [y] using hxu
  have hmassM := sum_intervalStieltjesIntegral_positiveVertex_tangent
    M hab hturn fM hmM E hE hEa
  have hmassK := sum_intervalStieltjesIntegral_positiveVertex_tangent
    K hab hturn fK hmK E hE hEa
  have hmassL := sum_intervalStieltjesIntegral_positiveVertex_tangent
    L hab hturn fL hmL E hE hEa
  rw [himage] at hmassM hmassK hmassL
  have hstieltjes (i : Fin 2) :
      intervalStieltjesIntegral (fM i)
          (fun x ↦ tangentVector ((((x : Set.Icc (0 : ℝ) (2 * Real.pi)) : ℝ) :
            Real.Angle)) i) E =
        r * intervalStieltjesIntegral (fK i)
            (fun x ↦ tangentVector ((((x : Set.Icc (0 : ℝ) (2 * Real.pi)) : ℝ) :
              Real.Angle)) i) E +
          s * intervalStieltjesIntegral (fL i)
            (fun x ↦ tangentVector ((((x : Set.Icc (0 : ℝ) (2 * Real.pi)) : ℝ) :
              Real.Angle)) i) E := by
    have hq : Continuous (fun x : Set.Icc (0 : ℝ) (2 * Real.pi) ↦
        tangentVector (((x : ℝ) : Real.Angle)) i) := by
      have hi : Continuous (fun u : Real.Angle ↦ tangentVector u i) := by
        fin_cases i
        · exact Real.Angle.continuous_sin.neg
        · exact Real.Angle.continuous_cos
      exact hi.comp (Real.Angle.continuous_coe.comp continuous_subtype_val)
    have hrint : (r • VectorMeasure.restrict (intervalStieltjesMeasure (fK i)) E).Integrable
        (fun x ↦ tangentVector (((x : ℝ) : Real.Angle)) i) :=
      ((fK i).integrable_of_continuous hq).integrableOn.smul_vectorMeasure r
    have hsint : (s • VectorMeasure.restrict (intervalStieltjesMeasure (fL i)) E).Integrable
        (fun x ↦ tangentVector (((x : ℝ) : Real.Angle)) i) :=
      ((fL i).integrable_of_continuous hq).integrableOn.smul_vectorMeasure s
    unfold intervalStieltjesIntegral
    rw [hmeasure i, VectorMeasure.restrict_add, VectorMeasure.restrict_smul,
      VectorMeasure.restrict_smul, VectorMeasure.integral_add_vectorMeasure hrint hsint,
      VectorMeasure.integral_smul_vectorMeasure, VectorMeasure.integral_smul_vectorMeasure]
    rfl
  have hreal : (surfaceAreaMeasure M A).toReal =
      r * (surfaceAreaMeasure K A).toReal + s * (surfaceAreaMeasure L A).toReal := by
    rw [← hmassM, ← hmassK, ← hmassL, Fin.sum_univ_two]
    rw [hstieltjes 0, hstieltjes 1]
    simp only [Fin.sum_univ_two]
    ring
  let _ : IsFiniteMeasure (surfaceAreaMeasure M) := (surfaceAreaMeasure_face_union M).1
  let _ : IsFiniteMeasure (surfaceAreaMeasure K) := (surfaceAreaMeasure_face_union K).1
  let _ : IsFiniteMeasure (surfaceAreaMeasure L) := (surfaceAreaMeasure_face_union L).1
  have hKtop : surfaceAreaMeasure K A ≠ ⊤ := measure_ne_top _ A
  have hLtop : surfaceAreaMeasure L A ≠ ⊤ := measure_ne_top _ A
  have hright :
      (ENNReal.ofReal (1 - (t : ℝ)) • surfaceAreaMeasure K +
        ENNReal.ofReal (t : ℝ) • surfaceAreaMeasure L) A ≠ ⊤ := by
    rw [Measure.add_apply]
    simp only [Measure.smul_apply]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKtop,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hLtop⟩
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ A) hright).mp
  rw [show convexBodyCombination t K L = M from rfl, hreal]
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.toReal_add
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKtop)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hLtop),
    ENNReal.toReal_mul, ENNReal.toReal_mul]
  rw [ENNReal.toReal_ofReal (sub_nonneg.mpr t.2.2), ENNReal.toReal_ofReal t.2.1]

end MovingSofa
