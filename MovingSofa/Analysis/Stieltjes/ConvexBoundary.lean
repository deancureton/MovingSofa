import MovingSofa.Convex.BoundaryApproximation
import MovingSofa.Geometry.ContactGeometry
import MovingSofa.Analysis.Stieltjes.Integral

noncomputable section

open scoped Topology

namespace MovingSofa

/-- Each coordinate of the positive vertex is right-continuous and has bounded
variation on its closed interval domain. -/
theorem exists_positiveVertex_intervalBV (K : ConvexBody Point) {a b : ℝ} (hab : a ≤ b) :
    ∃ f : Fin 2 → RightContinuousIntervalBV a b,
      ∀ i t, (f i).toFun t = (edgeVertices K ((t : ℝ) : Real.Angle)).1 i := by
  have hv : BoundedVariationOn
      (fun t : Set.Icc a b ↦ (edgeVertices K ((t : ℝ) : Real.Angle)).1) Set.univ := by
    exact ne_top_of_le_ne_top (positiveVertex_boundedVariation K a b hab)
      (eVariationOn.comp_le_of_monotoneOn
        (fun t : ℝ ↦ (edgeVertices K (t : Real.Angle)).1)
        (s := Set.Icc a b) (t := Set.univ) (fun t : Set.Icc a b ↦ (t : ℝ))
        (fun _ _ _ _ h ↦ h) (fun t _ ↦ t.property))
  have hc (i : Fin 2) : IsIntervalBoundedVariation a b
      (fun t : Set.Icc a b ↦ (edgeVertices K ((t : ℝ) : Real.Angle)).1 i) := by
    change BoundedVariationOn ((fun p : Point ↦ p i) ∘
      fun t : Set.Icc a b ↦ (edgeVertices K ((t : ℝ) : Real.Angle)).1) Set.univ
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) i).lipschitzWith.comp_boundedVariationOn
      (g := fun t : Set.Icc a b ↦ (edgeVertices K ((t : ℝ) : Real.Angle)).1) hv
  have hr (i : Fin 2) (t : Set.Icc a b) : ContinuousWithinAt
      (fun s : Set.Icc a b ↦ (edgeVertices K ((s : ℝ) : Real.Angle)).1 i)
      (Set.Ici t) t := by
    have h : ContinuousWithinAt (fun s : ℝ ↦ (edgeVertices K (s : Real.Angle)).1)
        (Set.Ici (t : ℝ)) (t : ℝ) :=
      continuousWithinAt_Ioi_iff_Ici.mp (contact_oneSided_limits K (t : ℝ)).1
    have hcomp : ContinuousWithinAt
        (fun s : Set.Icc a b ↦ (edgeVertices K ((s : ℝ) : Real.Angle)).1)
        (Set.Ici t) t := h.comp
      (show ContinuousWithinAt (fun s : Set.Icc a b ↦ (s : ℝ)) (Set.Ici t) t from
        continuous_subtype_val.continuousWithinAt) (fun _ hy ↦ hy)
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) i).continuous.continuousAt
      |>.comp_continuousWithinAt hcomp
  exact ⟨fun i ↦ ⟨_, hc i, hr i⟩, fun _ _ ↦ rfl⟩

/-- Each coordinate of the positive vertex is measurable on the closed parameter interval,
being the difference of two monotone functions by bounded variation. -/
theorem measurable_positiveVertex_coordinate (K : ConvexBody Point) {a b : ℝ}
    (hab : a ≤ b) (i : Fin 2) :
    Measurable fun t : Set.Icc a b ↦ (edgeVertices K (((t : ℝ) : Real.Angle))).1 i := by
  obtain ⟨f, hf⟩ := exists_positiveVertex_intervalBV K hab
  have hfun : (fun t : Set.Icc a b ↦ (edgeVertices K (((t : ℝ) : Real.Angle))).1 i) =
      (f i).toFun := by
    funext t
    exact (hf i t).symm
  have hbv : LocallyBoundedVariationOn (f i).toFun (Set.univ : Set (Set.Icc a b)) :=
    (f i).boundedVariation.locallyBoundedVariationOn
  obtain ⟨p, q, hp, hq, hpq⟩ := hbv.exists_monotoneOn_sub_monotoneOn
  rw [hfun, hpq]
  exact (monotoneOn_univ.mp hp).measurable.sub (monotoneOn_univ.mp hq).measurable

/-- Each coordinate of the positive vertex is measurable on the half-open parameter
interval. -/
theorem measurable_positiveVertex_coordinate_Ioc (K : ConvexBody Point) {a b : ℝ}
    (hab : a ≤ b) (i : Fin 2) :
    Measurable fun t : Set.Ioc a b ↦ (edgeVertices K (((t : ℝ) : Real.Angle))).1 i := by
  have hpos := measurable_positiveVertex_coordinate K hab i
  have hmem (t : Set.Ioc a b) : (t : ℝ) ∈ Set.Icc a b := ⟨t.property.1.le, t.property.2⟩
  have hcont : Continuous fun t : Set.Ioc a b ↦ (⟨(t : ℝ), hmem t⟩ : Set.Icc a b) :=
    Continuous.subtype_mk continuous_subtype_val hmem
  have hcomp : Measurable
      ((fun s : Set.Icc a b ↦ (edgeVertices K (((s : ℝ) : Real.Angle))).1 i) ∘
        fun t : Set.Ioc a b ↦ (⟨(t : ℝ), hmem t⟩ : Set.Icc a b)) :=
    hpos.comp hcont.measurable
  have hfun : ((fun s : Set.Icc a b ↦ (edgeVertices K (((s : ℝ) : Real.Angle))).1 i) ∘
      fun t : Set.Ioc a b ↦ (⟨(t : ℝ), hmem t⟩ : Set.Icc a b)) =
      fun t : Set.Ioc a b ↦ (edgeVertices K (((t : ℝ) : Real.Angle))).1 i := by
    funext t
    rfl
  rwa [hfun] at hcomp

/-- Each coordinate of the negative vertex is measurable on the half-open parameter interval,
being the pointwise left limit of the positive vertex. -/
theorem measurable_negativeVertex_coordinate (K : ConvexBody Point) {a b : ℝ}
    (hab : a ≤ b) (i : Fin 2) :
    Measurable fun t : Set.Ioc a b ↦ (edgeVertices K (((t : ℝ) : Real.Angle))).2 i := by
  have hpos := measurable_positiveVertex_coordinate K hab i
  have hmem (n : ℕ) (t : Set.Ioc a b) :
      max a ((t : ℝ) - 1 / (n + 1 : ℝ)) ∈ Set.Icc a b := by
    refine ⟨le_max_left _ _, max_le hab ?_⟩
    have : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
    linarith [t.property.2]
  set g : ℕ → Set.Ioc a b → ℝ := fun n t ↦
    (edgeVertices K ((max a ((t : ℝ) - 1 / (n + 1 : ℝ)) : ℝ) : Real.Angle)).1 i
  have hgmeas (n : ℕ) : Measurable (g n) := by
    have hcont : Continuous fun t : Set.Ioc a b ↦ (⟨max a ((t : ℝ) - 1 / (n + 1 : ℝ)),
        hmem n t⟩ : Set.Icc a b) :=
      Continuous.subtype_mk
        (continuous_const.max (continuous_subtype_val.sub continuous_const)) (hmem n)
    have hcomp : Measurable
        ((fun s : Set.Icc a b ↦ (edgeVertices K (((s : ℝ) : Real.Angle))).1 i) ∘
          fun t : Set.Ioc a b ↦ (⟨max a ((t : ℝ) - 1 / (n + 1 : ℝ)),
            hmem n t⟩ : Set.Icc a b)) :=
      hpos.comp hcont.measurable
    have hfun :
        ((fun s : Set.Icc a b ↦ (edgeVertices K (((s : ℝ) : Real.Angle))).1 i) ∘
          fun t : Set.Ioc a b ↦ (⟨max a ((t : ℝ) - 1 / (n + 1 : ℝ)),
            hmem n t⟩ : Set.Icc a b)) = g n := by
      funext t
      rfl
    rwa [hfun] at hcomp
  refine measurable_of_tendsto_metrizable hgmeas (tendsto_pi_nhds.2 fun t ↦ ?_)
  have hta : a < (t : ℝ) := t.property.1
  have hlim := (contact_oneSided_limits K (t : ℝ)).2.2.2.1
  have hlimi : Filter.Tendsto (fun s : ℝ ↦ (edgeVertices K (s : Real.Angle)).1 i)
      (𝓝[<] (t : ℝ)) (𝓝 ((edgeVertices K ((t : ℝ) : Real.Angle)).2 i)) :=
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) i).continuous.tendsto _).comp hlim
  refine hlimi.comp ?_
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have h0 : Filter.Tendsto (fun n : ℕ ↦ (t : ℝ) - 1 / (n + 1 : ℝ))
        Filter.atTop (𝓝 (t : ℝ)) := by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_sub ((t : ℝ))
    have hconst : Filter.Tendsto (fun _ : ℕ ↦ a) Filter.atTop (𝓝 a) := tendsto_const_nhds
    have h1 := hconst.max h0
    rwa [max_eq_right hta.le] at h1
  · obtain ⟨N, hN⟩ := exists_nat_gt (1 / ((t : ℝ) - a))
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    have hpos : (0 : ℝ) < (t : ℝ) - a := by linarith
    have hNle : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hn
    have hlt : 1 / (n + 1 : ℝ) < (t : ℝ) - a := by
      have h1 : 1 / ((t : ℝ) - a) < (n + 1 : ℝ) := by linarith
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (n + 1 : ℝ))]
      rw [div_lt_iff₀ hpos] at h1
      linarith
    have hmaxeq : max a ((t : ℝ) - 1 / (n + 1 : ℝ)) = (t : ℝ) - 1 / (n + 1 : ℝ) :=
      max_eq_right (by linarith)
    rw [Set.mem_Iio, hmaxeq]
    have : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
    linarith

end MovingSofa
