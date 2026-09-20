import MovingSofa.Analysis.SurfaceMeasure.VertexBoundary
import MovingSofa.Analysis.SurfaceMeasure.WeightedBoundary
import MovingSofa.Analysis.Stieltjes.DensityIntegration
import MovingSofa.Analysis.Stieltjes.Smooth
import MovingSofa.ForMathlib.MeasureTheory.Integral.Translation

/-!
# Angular densities of the surface-area measure

On an angular window of at most one turn the positive vertex of a convex body is a function of
bounded variation whose Stieltjes measure, paired with the moving tangent, is the surface-area
measure (`sum_intervalStieltjesIntegral_positiveVertex_tangent`).  If on such a window the
positive vertex happens to be a differentiable curve with derivative `g s • tangentVector s`,
this identifies the surface-area measure with the Lebesgue density `g`.

This file records that identification (`surfaceAreaMeasure_angleImage_eq_setLIntegral`,
`surfaceAreaMeasure_angleImage_eq_withDensity_of_hasDerivAt`), and the bookkeeping that glues
finitely many or countably many such windows together (`measure_angleImage_eq_of_union`,
`measure_angleImage_eq_of_iUnion`) and turns the resulting set-level identities into the
`Measure.restrict = Measure.map (Measure.withDensity …)` form used by cap-density statements
(`measure_restrict_eq_map_withDensity`, `surfaceAreaMeasure_restrict_eq_map_withDensity`,
`surfaceAreaMeasure_restrict_eq_map_add_withDensity`).

The gluing lemmas are stated for an arbitrary pair of measures on `Real.Angle` and on `ℝ`,
since they only use additivity and the injectivity of the angular projection on a window of at
most one turn.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace MovingSofa

/-- Pairing the frame tangent with a multiple of itself, in coordinates. -/
private theorem sum_mul_tangentVector_sq (c s : ℝ) :
    tangentVector (s : Real.Angle) 0 * (c * tangentVector (s : Real.Angle) 0) +
      tangentVector (s : Real.Angle) 1 * (c * tangentVector (s : Real.Angle) 1) = c := by
  have h : tangentVector (s : Real.Angle) 0 ^ 2 + tangentVector (s : Real.Angle) 1 ^ 2 = 1 := by
    have h := inner_tangentVector_self s
    rw [PiLp.inner_apply] at h
    simpa [Fin.sum_univ_two] using h
  linear_combination c * h

/-! ### The surface measure of an arc with a differentiable positive vertex -/

/-- Suppose that on the angular window `Ioc a b`, of at most one turn, the positive vertex of `K`
is traced by a curve `F` with derivative `g s • tangentVector s`, where `g` is continuous and
nonnegative.  Then the surface-area measure of the angular image of a measurable
`S ⊆ Ioc a b` is the Lebesgue integral of `g` over `S`. -/
theorem surfaceAreaMeasure_angleImage_eq_setLIntegral (K : ConvexBody Point) {a b : ℝ}
    (hab : a < b) (hturn : b ≤ a + 2 * Real.pi) (F : ℝ → Point) (g : ℝ → ℝ)
    (hF : ∀ s, HasDerivAt F (g s • tangentVector (s : Real.Angle)) s) (hg : Continuous g)
    (hgnn : ∀ s ∈ Ioc a b, 0 ≤ g s)
    (hvertex : ∀ s ∈ Icc a b, (edgeVertices K (s : Real.Angle)).1 = F s)
    {S : Set ℝ} (hS : MeasurableSet S) (hSsub : S ⊆ Ioc a b) :
    surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
      ∫⁻ s in S, ENNReal.ofReal (g s) := by
  have hfin : IsFiniteMeasure (surfaceAreaMeasure K) := (surfaceAreaMeasure_face_union K).1
  have hSIcc : S ⊆ Icc a b := hSsub.trans Ioc_subset_Icc_self
  obtain ⟨f, hftoFun, hfmeas⟩ := positiveVertex_stieltjes_surface K a b hab hturn
  have hcontT : ∀ i : Fin 2, Continuous fun s : ℝ ↦ tangentVector (s : Real.Angle) i :=
    fun i ↦ (continuous_tangentVector_coordinate i).comp Real.Angle.continuous_coe
  -- the coordinate functions of the differentiable vertex curve and their derivatives
  set φ : Fin 2 → ℝ → ℝ := fun i s ↦ F s i with hφ
  set ψ : Fin 2 → ℝ → ℝ := fun i s ↦ g s * tangentVector (s : Real.Angle) i with hψ
  have hderiv : ∀ (i : Fin 2) (s : ℝ), HasDerivAt (φ i) (ψ i s) s := by
    intro i s
    have h := (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp_hasDerivAt s (hF s)
    simpa [φ, ψ, Function.comp_def] using h
  have hcontψ : ∀ i : Fin 2, Continuous (ψ i) := fun i ↦ hg.mul (hcontT i)
  -- the Stieltjes density of each vertex coordinate
  have hdens : ∀ i : Fin 2, HasIntervalStieltjesDensity (f i) (ψ i) := by
    intro i
    obtain ⟨G, hGfun, hGdens⟩ :=
      exists_intervalBV_of_hasDerivAt hab.le (φ i) (ψ i) (hderiv i) (hcontψ i)
    have hfe : f i = G := by
      refine RightContinuousIntervalBV.toFun_injective (funext fun t ↦ ?_)
      rw [hftoFun i t, hGfun t, hvertex (t : ℝ) t.2]
    rw [hfe]
    exact hGdens
  -- the sum over the two coordinates of the Stieltjes integrals
  set E : Set (Icc a b) := {x : Icc a b | (x : ℝ) ∈ S} with hE
  have hEmeas : MeasurableSet E := hS.preimage measurable_subtype_coe
  have hEa : ∀ t ∈ E, a < (t : ℝ) := fun t ht ↦ (hSsub ht).1
  have himage : (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E =
      (fun s : ℝ ↦ (s : Real.Angle)) '' S := by
    ext u
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨(t : ℝ), ht, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s, hSIcc hs⟩, hs, rfl⟩
  have hsum := sum_intervalStieltjesIntegral_positiveVertex_tangent K hab hturn f hfmeas
    E hEmeas hEa
  rw [himage] at hsum
  -- each Stieltjes integral is an ordinary set integral
  have hstep : ∀ i : Fin 2,
      intervalStieltjesIntegral (f i) (fun t ↦ tangentVector ((t : ℝ) : Real.Angle) i) E =
        ∫ s in S, tangentVector (s : Real.Angle) i * ψ i s := by
    intro i
    have hq : Continuous fun t : Icc a b ↦ tangentVector ((t : ℝ) : Real.Angle) i :=
      (hcontT i).comp continuous_subtype_val
    rw [intervalStieltjesIntegral_eq_integral_mul_of_density (f i) (hdens i) hq E hEmeas]
    rw [MeasureTheory.integral_subtype_preimage measurableSet_Icc hS
      (fun s ↦ tangentVector (s : Real.Angle) i * ψ i s)]
    rw [Measure.restrict_restrict_of_subset hSIcc]
  simp only [hstep] at hsum
  -- integrability of the two summands and of the density
  have hintegrand : ∀ i : Fin 2,
      IntegrableOn (fun s : ℝ ↦ tangentVector (s : Real.Angle) i * ψ i s) S volume := by
    intro i
    refine (ContinuousOn.integrableOn_compact isCompact_Icc ?_).mono_set hSIcc
    exact ((hcontT i).mul (hcontψ i)).continuousOn
  have hgint : IntegrableOn g S volume :=
    (ContinuousOn.integrableOn_compact isCompact_Icc hg.continuousOn).mono_set hSIcc
  have hsum2 : (surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S)).toReal =
      ∫ s in S, g s := by
    rw [← hsum, Fin.sum_univ_two, ← integral_add (hintegrand 0) (hintegrand 1)]
    refine setIntegral_congr_fun hS fun s _ ↦ ?_
    exact sum_mul_tangentVector_sq (g s) s
  rw [← ENNReal.ofReal_toReal (measure_ne_top (surfaceAreaMeasure K) _), hsum2]
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hgint]
  filter_upwards [ae_restrict_mem hS] with s hs
  exact hgnn s (hSsub hs)

/-- The same identification as `surfaceAreaMeasure_angleImage_eq_setLIntegral`, phrased as
agreement with a `Measure.withDensity` for any nonnegative weight `w` that agrees with the
derivative factor `g` on the window. -/
theorem surfaceAreaMeasure_angleImage_eq_withDensity_of_hasDerivAt (K : ConvexBody Point)
    {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi) (F : ℝ → Point) (g w : ℝ → ℝ)
    (hF : ∀ s, HasDerivAt F (g s • tangentVector (s : Real.Angle)) s) (hg : Continuous g)
    (hvertex : ∀ s ∈ Icc a b, (edgeVertices K (s : Real.Angle)).1 = F s)
    (hw : ∀ s ∈ Ioc a b, w s = g s) (hwnn : ∀ s ∈ Ioc a b, 0 ≤ w s)
    (S : Set ℝ) (hS : MeasurableSet S) (hSsub : S ⊆ Ioc a b) :
    surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
      volume.withDensity (fun s ↦ ENNReal.ofReal (w s)) S := by
  have hgnn : ∀ s ∈ Ioc a b, 0 ≤ g s := fun s hs ↦ (hw s hs) ▸ hwnn s hs
  rw [withDensity_apply _ hS, surfaceAreaMeasure_angleImage_eq_setLIntegral K hab hturn F g hF hg
    hgnn hvertex hS hSsub]
  exact setLIntegral_congr_fun hS fun s hs ↦ by rw [hw s (hSsub hs)]

/-! ### Gluing angular density identities -/

/-- Two measures that read one another through the angular projection on each of two disjoint
measurable subsets of a window of at most one turn do so on their union. -/
theorem measure_angleImage_eq_of_union {μ : Measure Real.Angle} {ν : Measure ℝ} {c d : ℝ}
    (hturn : d ≤ c + 2 * Real.pi) {I J : Set ℝ}
    (hI : I ⊆ Ioc c d) (hJ : J ⊆ Ioc c d)
    (hImeas : MeasurableSet I) (hJmeas : MeasurableSet J) (hdisj : Disjoint I J)
    (hA : ∀ S, MeasurableSet S → S ⊆ I → μ ((fun s : ℝ ↦ (s : Real.Angle)) '' S) = ν S)
    (hB : ∀ S, MeasurableSet S → S ⊆ J → μ ((fun s : ℝ ↦ (s : Real.Angle)) '' S) = ν S)
    (S : Set ℝ) (hS : MeasurableSet S) (hSsub : S ⊆ I ∪ J) :
    μ ((fun s : ℝ ↦ (s : Real.Angle)) '' S) = ν S := by
  have hsplit : S = S ∩ I ∪ S ∩ J := by
    rw [← Set.inter_union_distrib_left, Set.inter_eq_left.2 hSsub]
  have hSI : MeasurableSet (S ∩ I) := hS.inter hImeas
  have hSJ : MeasurableSet (S ∩ J) := hS.inter hJmeas
  have hdisj' : Disjoint (S ∩ I) (S ∩ J) :=
    hdisj.mono Set.inter_subset_right Set.inter_subset_right
  have hinj := Real.Angle.injOn_coe_Ioc hturn
  have himdisj : Disjoint ((fun s : ℝ ↦ (s : Real.Angle)) '' (S ∩ I))
      ((fun s : ℝ ↦ (s : Real.Angle)) '' (S ∩ J)) := by
    rw [Set.disjoint_left]
    rintro u ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have hyx : y = x := hinj (hJ hy.2) (hI hx.2) hxy
    exact (Set.disjoint_left.1 hdisj' hx) (hyx ▸ hy)
  have himmeas : MeasurableSet ((fun s : ℝ ↦ (s : Real.Angle)) '' (S ∩ J)) :=
    Real.Angle.measurableSet_image_of_subset_Ioc hturn hSJ (Set.inter_subset_right.trans hJ)
  calc μ ((fun s : ℝ ↦ (s : Real.Angle)) '' S)
      = μ ((fun s : ℝ ↦ (s : Real.Angle)) '' (S ∩ I) ∪
          (fun s : ℝ ↦ (s : Real.Angle)) '' (S ∩ J)) := by
        rw [← Set.image_union, ← hsplit]
    _ = μ ((fun s : ℝ ↦ (s : Real.Angle)) '' (S ∩ I)) +
          μ ((fun s : ℝ ↦ (s : Real.Angle)) '' (S ∩ J)) := measure_union himdisj himmeas
    _ = ν (S ∩ I) + ν (S ∩ J) := by
        rw [hA _ hSI Set.inter_subset_right, hB _ hSJ Set.inter_subset_right]
    _ = ν S := by rw [← measure_union hdisj' hSJ, ← hsplit]

/-- Two measures that read one another through the angular projection on each member of a
monotone sequence of measurable sets do so on the union of that sequence. -/
theorem measure_angleImage_eq_of_iUnion {μ : Measure Real.Angle} {ν : Measure ℝ}
    {J : ℕ → Set ℝ} (hmono : Monotone J) (hJmeas : ∀ n, MeasurableSet (J n))
    (hA : ∀ (n : ℕ) (S : Set ℝ), MeasurableSet S → S ⊆ J n →
      μ ((fun s : ℝ ↦ (s : Real.Angle)) '' S) = ν S)
    (S : Set ℝ) (hS : MeasurableSet S) (hSsub : S ⊆ ⋃ n, J n) :
    μ ((fun s : ℝ ↦ (s : Real.Angle)) '' S) = ν S := by
  have hSeq : S = ⋃ n, S ∩ J n := by
    rw [← Set.inter_iUnion, Set.inter_eq_left.2 hSsub]
  have hmono' : Monotone fun n ↦ S ∩ J n := fun m n h ↦
    Set.inter_subset_inter_right _ (hmono h)
  have hmonoimg : Monotone fun n ↦ (fun s : ℝ ↦ (s : Real.Angle)) '' (S ∩ J n) :=
    fun m n h ↦ Set.image_mono (hmono' h)
  calc μ ((fun s : ℝ ↦ (s : Real.Angle)) '' S)
      = μ (⋃ n, (fun s : ℝ ↦ (s : Real.Angle)) '' (S ∩ J n)) := by
        rw [← Set.image_iUnion, ← hSeq]
    _ = ⨆ n, μ ((fun s : ℝ ↦ (s : Real.Angle)) '' (S ∩ J n)) := hmonoimg.measure_iUnion
    _ = ⨆ n, ν (S ∩ J n) :=
        iSup_congr fun n ↦ hA n _ (hS.inter (hJmeas n)) Set.inter_subset_right
    _ = ν S := by rw [← hmono'.measure_iUnion, ← hSeq]

/-! ### From set-level identities to restricted measures -/

/-- A set-level angular density identity on a measurable parameter set `I` says exactly that the
measure restricted to the angular image of `I` is the pushforward of the weighted Lebesgue
measure on `I`. -/
theorem measure_restrict_eq_map_withDensity {μ : Measure Real.Angle} {I : Set ℝ}
    {w : ℝ → ℝ≥0∞} (hImeas : MeasurableSet I)
    (hagree : ∀ S, MeasurableSet S → S ⊆ I →
      μ ((fun s : ℝ ↦ (s : Real.Angle)) '' S) = volume.withDensity w S) :
    μ.restrict ((fun s : ℝ ↦ (s : Real.Angle)) '' I) =
      Measure.map (fun s : ℝ ↦ (s : Real.Angle)) ((volume.restrict I).withDensity w) := by
  have hmeas : Measurable fun s : ℝ ↦ (s : Real.Angle) := Real.Angle.continuous_coe.measurable
  ext B hB
  have hpre : MeasurableSet ((fun s : ℝ ↦ (s : Real.Angle)) ⁻¹' B) := hB.preimage hmeas
  have hset : B ∩ (fun s : ℝ ↦ (s : Real.Angle)) '' I =
      (fun s : ℝ ↦ (s : Real.Angle)) '' ((fun s : ℝ ↦ (s : Real.Angle)) ⁻¹' B ∩ I) := by
    ext u
    constructor
    · rintro ⟨hu, s, hs, rfl⟩
      exact ⟨s, ⟨hu, hs⟩, rfl⟩
    · rintro ⟨s, ⟨hs1, hs2⟩, rfl⟩
      exact ⟨hs1, s, hs2, rfl⟩
  rw [Measure.restrict_apply hB, hset, hagree _ (hpre.inter hImeas) Set.inter_subset_right,
    Measure.map_apply hmeas hB, withDensity_apply _ hpre,
    withDensity_apply _ (hpre.inter hImeas), Measure.restrict_restrict hpre]

/-- The surface-area measure instance of `measure_restrict_eq_map_withDensity`. -/
theorem surfaceAreaMeasure_restrict_eq_map_withDensity {K : ConvexBody Point}
    {I : Set ℝ} {w : ℝ → ℝ≥0∞} (hImeas : MeasurableSet I)
    (hagree : ∀ S, MeasurableSet S → S ⊆ I →
      surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S) = volume.withDensity w S) :
    (surfaceAreaMeasure K).restrict ((fun s : ℝ ↦ (s : Real.Angle)) '' I) =
      Measure.map (fun s : ℝ ↦ (s : Real.Angle)) ((volume.restrict I).withDensity w) :=
  measure_restrict_eq_map_withDensity hImeas hagree

/-- The shifted form of `surfaceAreaMeasure_restrict_eq_map_withDensity`: an angular density
identity on the translated window `Ioc c (c + T)` with the translated weight `u ↦ w (u - c)`
says that the surface-area measure restricted to that angular arc is the pushforward of the
`w`-weighted Lebesgue measure on `Ioc 0 T` along `t ↦ ↑(t + c)`. -/
theorem surfaceAreaMeasure_restrict_eq_map_add_withDensity {K : ConvexBody Point}
    {c T : ℝ} {w : ℝ → ℝ≥0∞}
    (hagree : ∀ S, MeasurableSet S → S ⊆ Ioc c (c + T) →
      surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
        volume.withDensity (fun u ↦ w (u - c)) S) :
    (surfaceAreaMeasure K).restrict ((fun s : ℝ ↦ (s : Real.Angle)) '' Ioc c (c + T)) =
      Measure.map (fun t : ℝ ↦ ((t + c : ℝ) : Real.Angle))
        ((volume.restrict (Ioc 0 T)).withDensity w) := by
  have hmeas : Measurable fun s : ℝ ↦ (s : Real.Angle) := Real.Angle.continuous_coe.measurable
  have hmeas' : Measurable fun t : ℝ ↦ ((t + c : ℝ) : Real.Angle) :=
    Real.Angle.continuous_coe.measurable.comp (measurable_id.add_const c)
  ext B hB
  have hpre : MeasurableSet ((fun s : ℝ ↦ (s : Real.Angle)) ⁻¹' B) := hB.preimage hmeas
  have hpre' : MeasurableSet ((fun t : ℝ ↦ ((t + c : ℝ) : Real.Angle)) ⁻¹' B) :=
    hB.preimage hmeas'
  have hset : B ∩ (fun s : ℝ ↦ (s : Real.Angle)) '' Ioc c (c + T) =
      (fun s : ℝ ↦ (s : Real.Angle)) ''
        ((fun s : ℝ ↦ (s : Real.Angle)) ⁻¹' B ∩ Ioc c (c + T)) := by
    ext u
    constructor
    · rintro ⟨hu, s, hs, rfl⟩
      exact ⟨s, ⟨hu, hs⟩, rfl⟩
    · rintro ⟨s, ⟨hs1, hs2⟩, rfl⟩
      exact ⟨hs1, s, hs2, rfl⟩
  have hpreimage : (fun t : ℝ ↦ t + c) ⁻¹'
      ((fun s : ℝ ↦ (s : Real.Angle)) ⁻¹' B ∩ Ioc c (c + T)) =
      (fun t : ℝ ↦ ((t + c : ℝ) : Real.Angle)) ⁻¹' B ∩ Ioc 0 T := by
    ext t
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_Ioc]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, by linarith, by linarith⟩
  rw [Measure.restrict_apply hB, hset,
    hagree _ (hpre.inter measurableSet_Ioc) Set.inter_subset_right,
    withDensity_apply _ (hpre.inter measurableSet_Ioc), setLIntegral_comp_sub_right, hpreimage,
    Measure.map_apply hmeas' hB, withDensity_apply _ hpre',
    Measure.restrict_restrict hpre']

end MovingSofa
