import MovingSofa.Analysis.SurfaceMeasure.AngularDensity
import MovingSofa.Analysis.SurfaceMeasure.Opposite
import MovingSofa.ForMathlib.MeasureTheory.Measure.Atoms

/-!
# Angular densities of the opposite surface measure

The opposite surface measure `(oppositeSurfaceData K).1` is the surface-area measure of `K`
translated by `π`, so it reads the *negative* vertex data of `K` at the angle `s` as the positive
vertex data at `π + s`.  Transporting `surfaceAreaMeasure_angleImage_eq_setLIntegral` along that
translation identifies it with a Lebesgue density whenever the positive vertex of `K` at normal
`π + s` is traced by a differentiable curve `F` with derivative `-(g s) • tangentVector s`
(`oppositeSurfaceData_angleImage_eq_withDensity`); the extra minus sign is exactly
`tangentVector_add_pi`.

The two variants `oppositeSurfaceData_angleImage_eq_withDensity_of_openLeft` and
`…_of_openRight` drop the vertex information at one endpoint of the window by exhausting the
window from the other side with `measure_angleImage_eq_of_iUnion`.
-/

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- An Archimedean step used to exhaust an open interval endpoint. -/
private theorem exists_nat_div_add_two_lt {d e : ℝ} (he : 0 < e) :
    ∃ n : ℕ, d / (n + 2) < e := by
  obtain ⟨n, hn⟩ := exists_nat_gt (d / e)
  refine ⟨n, ?_⟩
  have hpos : (0 : ℝ) < n + 2 := by positivity
  rw [div_lt_iff₀ hpos]
  have h : d / e < n + 2 := by linarith
  rw [div_lt_iff₀ he] at h
  linarith

/-- The angular projection reads the opposite surface measure through the `π`-shifted window. -/
theorem oppositeSurfaceData_angleImage (K : ConvexBody Point) {S : Set ℝ}
    (hS : MeasurableSet ((fun s : ℝ ↦ (s : Real.Angle)) '' S)) :
    (oppositeSurfaceData K).1 ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
      surfaceAreaMeasure K
        ((fun s : ℝ ↦ (s : Real.Angle)) '' ((fun s : ℝ ↦ s + Real.pi) '' S)) := by
  have hm : Measurable fun t : Real.Angle ↦ t - ((Real.pi : ℝ) : Real.Angle) :=
    (continuous_id.sub continuous_const).measurable
  have hpre : (fun t : Real.Angle ↦ t - ((Real.pi : ℝ) : Real.Angle)) ⁻¹'
      ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
      (fun s : ℝ ↦ (s : Real.Angle)) '' ((fun s : ℝ ↦ s + Real.pi) '' S) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨s, hs, hsx⟩
      refine ⟨s + Real.pi, ⟨s, hs, rfl⟩, ?_⟩
      rw [Real.Angle.coe_add, hsx]
      abel
    · rintro ⟨r, ⟨s, hs, rfl⟩, rfl⟩
      refine ⟨s, hs, ?_⟩
      rw [Real.Angle.coe_add]
      abel
  show Measure.map (fun t : Real.Angle ↦ t - ((Real.pi : ℝ) : Real.Angle))
    (surfaceAreaMeasure K) _ = _
  rw [Measure.map_apply hm hS, hpre]

/-- Suppose that on the angular window `(π + a, π + b]`, of at most one turn, the positive vertex
of `K` at normal `π + s` is traced by a curve `F` with derivative `-(g s) • v_s`, where `g` is
continuous and nonnegative.  Then the opposite surface measure of the angular image of a
measurable `S ⊆ (a, b]` is the weighted Lebesgue measure of `S` for any weight `f` agreeing with
`g` on the open window. -/
theorem oppositeSurfaceData_angleImage_eq_withDensity (K : ConvexBody Point) {a b : ℝ}
    (hab : a < b) (hturn : b ≤ a + 2 * Real.pi) (F : ℝ → Point) (f g : ℝ → ℝ)
    (hF : ∀ s, HasDerivAt F (-(g s) • tangentVector (s : Real.Angle)) s) (hg : Continuous g)
    (hgnn : ∀ s ∈ Set.Ioc a b, 0 ≤ g s) (hfg : ∀ s ∈ Set.Ioo a b, f s = g s)
    (hvertex : ∀ s ∈ Set.Icc a b, (edgeVertices K ((Real.pi + s : ℝ) : Real.Angle)).1 = F s)
    {S : Set ℝ} (hS : MeasurableSet S) (hSsub : S ⊆ Set.Ioc a b) :
    (oppositeSurfaceData K).1 ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
      volume.withDensity (fun s ↦ ENNReal.ofReal (f s)) S := by
  have hemb : MeasurableEmbedding fun s : ℝ ↦ s + Real.pi :=
    (MeasurableEquiv.addRight Real.pi).measurableEmbedding
  have himg : MeasurableSet ((fun s : ℝ ↦ (s : Real.Angle)) '' S) :=
    Real.Angle.measurableSet_image_of_subset_Ioc hturn hS hSsub
  have hSmeas : MeasurableSet ((fun s : ℝ ↦ s + Real.pi) '' S) := hemb.measurableSet_image' hS
  have hSsub' : (fun s : ℝ ↦ s + Real.pi) '' S ⊆ Set.Ioc (a + Real.pi) (b + Real.pi) := by
    rintro r ⟨s, hs, rfl⟩
    exact ⟨by linarith [(hSsub hs).1], by linarith [(hSsub hs).2]⟩
  -- the vertex curve of the shifted window and its derivative
  have hshift : ∀ r : ℝ, tangentVector ((r - Real.pi : ℝ) : Real.Angle) =
      -tangentVector (r : Real.Angle) := by
    intro r
    have h := tangentVector_add_pi (r - Real.pi)
    rw [show r - Real.pi + Real.pi = r from by ring] at h
    rw [h, neg_neg]
  have hF' : ∀ r : ℝ, HasDerivAt (fun r : ℝ ↦ F (r - Real.pi))
      (g (r - Real.pi) • tangentVector (r : Real.Angle)) r := by
    intro r
    have h := (hF (r - Real.pi)).scomp r ((hasDerivAt_id r).sub_const Real.pi)
    rw [hshift r] at h
    refine h.congr_deriv ?_
    module
  have hvertex' : ∀ r ∈ Set.Icc (a + Real.pi) (b + Real.pi),
      (edgeVertices K (r : Real.Angle)).1 = F (r - Real.pi) := by
    intro r hr
    have h := hvertex (r - Real.pi) ⟨by linarith [hr.1], by linarith [hr.2]⟩
    rw [show Real.pi + (r - Real.pi) = r from by ring] at h
    exact h
  have hmain := surfaceAreaMeasure_angleImage_eq_setLIntegral K (a := a + Real.pi)
    (b := b + Real.pi) (by linarith) (by linarith) (fun r ↦ F (r - Real.pi))
    (fun r ↦ g (r - Real.pi)) hF' (hg.comp (continuous_id.sub continuous_const))
    (fun r hr ↦ hgnn (r - Real.pi) ⟨by linarith [hr.1], by linarith [hr.2]⟩) hvertex'
    hSmeas hSsub'
  -- change variables back to the unshifted window
  rw [oppositeSurfaceData_angleImage K himg, hmain,
    setLIntegral_comp_sub_right (fun s ↦ ENNReal.ofReal (g s)) Real.pi,
    hemb.injective.preimage_image, withDensity_apply _ hS]
  -- the two densities agree off the right endpoint
  refine (lintegral_congr_ae ?_).symm
  have hne : ∀ᵐ s ∂volume.restrict S, s ∈ Set.Ioo a b := by
    refine ae_restrict_mem_of_countable_diff hS (Set.countable_singleton b) ?_
    rintro s ⟨hs, hsA⟩
    have h := hSsub hs
    rcases eq_or_lt_of_le h.2 with heq | hlt
    · exact heq
    · exact absurd (Set.mem_Ioo.2 ⟨h.1, hlt⟩) hsA
  filter_upwards [hne] with s hs
  rw [hfg s hs]

/-- The variant of `oppositeSurfaceData_angleImage_eq_withDensity` whose left endpoint carries no
vertex information: the window is exhausted from the right. -/
theorem oppositeSurfaceData_angleImage_eq_withDensity_of_openLeft (K : ConvexBody Point)
    {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi) (F : ℝ → Point)
    (f g : ℝ → ℝ)
    (hF : ∀ s, HasDerivAt F (-(g s) • tangentVector (s : Real.Angle)) s) (hg : Continuous g)
    (hgnn : ∀ s ∈ Set.Ioc a b, 0 ≤ g s) (hfg : ∀ s ∈ Set.Ioo a b, f s = g s)
    (hvertex : ∀ s ∈ Set.Ioc a b, (edgeVertices K ((Real.pi + s : ℝ) : Real.Angle)).1 = F s)
    {S : Set ℝ} (hS : MeasurableSet S) (hSsub : S ⊆ Set.Ioc a b) :
    (oppositeSurfaceData K).1 ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
      volume.withDensity (fun s ↦ ENNReal.ofReal (f s)) S := by
  have hba : 0 < b - a := by linarith
  have hpos : ∀ n : ℕ, 0 < (b - a) / (n + 2) := fun n ↦ by positivity
  have hlt : ∀ n : ℕ, a + (b - a) / (n + 2) < b := by
    intro n
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h1 : (b - a) / ((n : ℝ) + 2) ≤ (b - a) / 2 := by gcongr; linarith
    linarith
  refine measure_angleImage_eq_of_iUnion (μ := (oppositeSurfaceData K).1)
    (J := fun n : ℕ ↦ Set.Ioc (a + (b - a) / (n + 2)) b)
    (ν := volume.withDensity (fun s ↦ ENNReal.ofReal (f s))) ?_ (fun n ↦ measurableSet_Ioc) ?_
    S hS ?_
  · intro m n hmn
    refine Set.Ioc_subset_Ioc ?_ le_rfl
    have hmn' : ((m : ℝ)) ≤ n := Nat.cast_le.2 hmn
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have h1 : (b - a) / ((n : ℝ) + 2) ≤ (b - a) / ((m : ℝ) + 2) := by gcongr
    linarith
  · intro n T hT hTsub
    refine oppositeSurfaceData_angleImage_eq_withDensity K (hlt n) (by linarith [hpos n])
      F f g hF hg (fun s hs ↦ hgnn s ⟨by linarith [hs.1, hpos n], hs.2⟩)
      (fun s hs ↦ hfg s ⟨by linarith [hs.1, hpos n], hs.2⟩)
      (fun s hs ↦ hvertex s ⟨by linarith [hs.1, hpos n], hs.2⟩) hT hTsub
  · intro s hs
    obtain ⟨n, hn⟩ := exists_nat_div_add_two_lt (d := b - a) (e := s - a)
      (by linarith [(hSsub hs).1])
    exact Set.mem_iUnion.2 ⟨n, ⟨by linarith, (hSsub hs).2⟩⟩

/-- The variant of `oppositeSurfaceData_angleImage_eq_withDensity` whose right endpoint carries no
vertex information: the window is exhausted from the left. -/
theorem oppositeSurfaceData_angleImage_eq_withDensity_of_openRight (K : ConvexBody Point)
    {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi) (F : ℝ → Point)
    (f g : ℝ → ℝ)
    (hF : ∀ s, HasDerivAt F (-(g s) • tangentVector (s : Real.Angle)) s) (hg : Continuous g)
    (hgnn : ∀ s ∈ Set.Ioo a b, 0 ≤ g s) (hfg : ∀ s ∈ Set.Ioo a b, f s = g s)
    (hvertex : ∀ s ∈ Set.Ico a b, (edgeVertices K ((Real.pi + s : ℝ) : Real.Angle)).1 = F s)
    {S : Set ℝ} (hS : MeasurableSet S) (hSsub : S ⊆ Set.Ioo a b) :
    (oppositeSurfaceData K).1 ((fun s : ℝ ↦ (s : Real.Angle)) '' S) =
      volume.withDensity (fun s ↦ ENNReal.ofReal (f s)) S := by
  have hba : 0 < b - a := by linarith
  have hpos : ∀ n : ℕ, 0 < (b - a) / (n + 2) := fun n ↦ by positivity
  have hlt : ∀ n : ℕ, a < b - (b - a) / (n + 2) := by
    intro n
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h1 : (b - a) / ((n : ℝ) + 2) ≤ (b - a) / 2 := by gcongr; linarith
    linarith
  refine measure_angleImage_eq_of_iUnion (μ := (oppositeSurfaceData K).1)
    (J := fun n : ℕ ↦ Set.Ioc a (b - (b - a) / (n + 2)))
    (ν := volume.withDensity (fun s ↦ ENNReal.ofReal (f s))) ?_ (fun n ↦ measurableSet_Ioc) ?_
    S hS ?_
  · intro m n hmn
    refine Set.Ioc_subset_Ioc le_rfl ?_
    have hmn' : ((m : ℝ)) ≤ n := Nat.cast_le.2 hmn
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have h1 : (b - a) / ((n : ℝ) + 2) ≤ (b - a) / ((m : ℝ) + 2) := by gcongr
    linarith
  · intro n T hT hTsub
    refine oppositeSurfaceData_angleImage_eq_withDensity K (hlt n) (by linarith [hpos n])
      F f g hF hg (fun s hs ↦ hgnn s ⟨hs.1, by linarith [hs.2, hpos n]⟩)
      (fun s hs ↦ hfg s ⟨hs.1, by linarith [hs.2, hpos n]⟩)
      (fun s hs ↦ hvertex s ⟨hs.1, by linarith [hs.2, hpos n]⟩) hT hTsub
  · intro s hs
    obtain ⟨n, hn⟩ := exists_nat_div_add_two_lt (d := b - a) (e := b - s)
      (by linarith [(hSsub hs).2])
    exact Set.mem_iUnion.2 ⟨n, ⟨(hSsub hs).1, by linarith⟩⟩

end MovingSofa
