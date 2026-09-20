import MovingSofa.ForMathlib.MeasureTheory.VectorMeasure.Interval
import MovingSofa.Analysis.SurfaceMeasure.Properties
import MovingSofa.Analysis.Stieltjes.AbsoluteContinuity
import Mathlib.MeasureTheory.Constructions.Polish.Basic

noncomputable section

open Set MeasureTheory
open scoped Topology

namespace MovingSofa

/-- Agreement of positive-vertex increments with tangent-coordinate surface integrals extends
from half-open subintervals to every measurable set avoiding the initial endpoint. -/
theorem intervalStieltjesMeasure_eq_surfaceIntegral_of_increment
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi)
    (f : Fin 2 → RightContinuousIntervalBV a b)
    (hf : ∀ i t, (f i).toFun t =
      (edgeVertices K (((t : Set.Icc a b) : ℝ) : Real.Angle)).1 i)
    (hinc : ∀ (c d : Set.Icc a b), c < d → ∀ i : Fin 2,
      (edgeVertices K (((d : Set.Icc a b) : ℝ) : Real.Angle)).1 i -
          (edgeVertices K (((c : Set.Icc a b) : ℝ) : Real.Angle)).1 i =
        ∫ u in (fun t : ℝ ↦ (t : Real.Angle)) '' Ioc (c : ℝ) d,
          tangentVector u i ∂surfaceAreaMeasure K) :
    ∀ (i : Fin 2) (E : Set (Set.Icc a b)), MeasurableSet E →
      (∀ t ∈ E, a < (t : ℝ)) →
      intervalStieltjesMeasure (f i) E =
        ∫ u in (fun t : Set.Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
          tangentVector u i ∂surfaceAreaMeasure K := by
  let A := Set.Ioc a b
  let c : A → Real.Angle := fun t ↦ ((t : ℝ) : Real.Angle)
  let j : A → Set.Icc a b := fun t ↦ ⟨t, t.property.1.le, t.property.2⟩
  have hc : MeasurableEmbedding c := by
    refine ⟨?_, (Real.Angle.continuous_coe.comp continuous_subtype_val).measurable, ?_⟩
    · intro x y hxy
      exact Subtype.ext (Real.Angle.injOn_coe_Ioc hturn x.property y.property hxy)
    · intro s hs
      let S : Set ℝ := Subtype.val '' s
      have hS : MeasurableSet S :=
        (MeasurableEmbedding.subtype_coe measurableSet_Ioc).measurableSet_image' hs
      have hSI : Set.InjOn (fun t : ℝ ↦ (t : Real.Angle)) S := by
        intro x hx y hy hxy
        obtain ⟨tx, htx, rfl⟩ := hx
        obtain ⟨ty, hty, rfl⟩ := hy
        exact Real.Angle.injOn_coe_Ioc hturn tx.property ty.property hxy
      have hm := hS.image_of_continuousOn_injOn Real.Angle.continuous_coe.continuousOn hSI
      convert hm using 1
      ext u
      simp [S, c]
  have hj : Measurable j := by fun_prop
  intro i E hE hEa
  let _ : IsFiniteMeasure (surfaceAreaMeasure K) :=
    (surfaceAreaMeasure_face_union K).1
  have hgi : Integrable (fun u : Real.Angle ↦ tangentVector u i) (surfaceAreaMeasure K) := by
    rw [← integrableOn_univ]
    exact ContinuousOn.integrableOn_compact isCompact_univ (by
      fin_cases i
      · exact Real.Angle.continuous_sin.neg.continuousOn
      · exact Real.Angle.continuous_cos.continuousOn)
  obtain ⟨ν, hν⟩ :=
    MeasurableEmbedding.exists_vectorMeasure_image_integral hc (surfaceAreaMeasure K)
      (fun u ↦ tangentVector u i) hgi
  have hmeasure : intervalStieltjesMeasure (f i) = ν.map j := by
    apply MeasureTheory.VectorMeasure.ext_of_Ioc
    · intro x y hxy
      have hpre : j ⁻¹' Ioc x y = {t : A | (x : ℝ) < (t : ℝ) ∧ (t : ℝ) ≤ (y : ℝ)} := rfl
      have hpremeas : MeasurableSet (j ⁻¹' Ioc x y) :=
        measurableSet_Ioc.preimage hj
      have himage : c '' (j ⁻¹' Ioc x y) =
          (fun t : ℝ ↦ (t : Real.Angle)) '' Ioc (x : ℝ) y := by
        ext u
        constructor
        · rintro ⟨t, ht, rfl⟩
          exact ⟨t, ht, rfl⟩
        · rintro ⟨t, ht, rfl⟩
          exact ⟨⟨t, x.property.1.trans_lt ht.1, ht.2.trans y.property.2⟩, ht, rfl⟩
      rw [intervalStieltjesMeasure_Ioc (f i) x y hxy.le,
        VectorMeasure.map_apply _ hj measurableSet_Ioc, hν _ hpremeas, himage,
        hf i y, hf i x, hinc x y hxy i]
    · let aa : Set.Icc a b := ⟨a, le_rfl, hab.le⟩
      let bb : Set.Icc a b := ⟨b, hab.le, le_rfl⟩
      have hpre : j ⁻¹' univ = univ := preimage_univ
      have hunivmeas : MeasurableSet (univ : Set A) := MeasurableSet.univ
      have himage : c '' (univ : Set A) =
          (fun t : ℝ ↦ (t : Real.Angle)) '' Ioc a b := by
        ext u
        simp [c, A]
      have hzero : intervalStieltjesMeasure (f i) {aa} = 0 := by
        rw [intervalStieltjesMeasure, (f i).boundedVariation.vectorMeasure_singleton,
          (f i).right_continuous aa |>.rightLim_eq]
        have hbot : 𝓝[<] aa = ⊥ := by
          have hIio : Iio aa = ∅ := by
            ext t
            simp only [mem_Iio, mem_empty_iff_false, iff_false]
            exact not_lt_of_ge t.property.1
          rw [hIio]
          exact nhdsWithin_empty aa
        rw [leftLim_eq_of_eq_bot _ hbot, sub_self]
      have hsplit : (univ : Set (Set.Icc a b)) = Ioc aa bb ∪ {aa} := by
        ext t
        simp only [mem_univ, true_iff, mem_union, mem_Ioc, mem_singleton_iff]
        by_cases hta : aa = t
        · exact Or.inr hta.symm
        · exact Or.inl ⟨lt_of_le_of_ne t.property.1 hta, t.property.2⟩
      have hlhs : intervalStieltjesMeasure (f i) univ =
          intervalStieltjesMeasure (f i) (Ioc aa bb) := by
        rw [hsplit, VectorMeasure.of_union (disjoint_singleton_right.2 (by simp))
          measurableSet_Ioc (measurableSet_singleton aa),
          hzero, add_zero]
      rw [hlhs, intervalStieltjesMeasure_Ioc (f i) aa bb hab.le,
        VectorMeasure.map_apply _ hj MeasurableSet.univ, hpre, hν _ hunivmeas, himage,
        hf i bb, hf i aa, hinc aa bb hab i]
  have himageE : c '' (j ⁻¹' E) =
      (fun t : Set.Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E := by
    ext u
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨j t, ht, rfl⟩
    · rintro ⟨t, htE, rfl⟩
      exact ⟨⟨t, hEa t htE, t.property.2⟩, htE, rfl⟩
  rw [hmeasure, VectorMeasure.map_apply _ hj hE, hν _ (hE.preimage hj), himageE]

end MovingSofa
