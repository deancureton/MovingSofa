import MovingSofa.ForMathlib.MeasureTheory.FiniteMeasure.Restriction
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

noncomputable section

open Filter Set MeasureTheory
open scoped Topology BoundedContinuousFunction

namespace Real.Angle

/-- A half-open interval of at most one turn has distinct angular representatives. -/
theorem injOn_coe_Ioc {a b : ℝ} (h : b ≤ a + 2 * Real.pi) :
    Set.InjOn (fun t : ℝ ↦ (t : Angle)) (Ioc a b) := by
  let : Fact (0 < 2 * Real.pi) := ⟨mul_pos (by norm_num) Real.pi_pos⟩
  intro x hx y hy hxy
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ioc
    ⟨hx.1, hx.2.trans h⟩ ⟨hy.1, hy.2.trans h⟩).mp hxy

/-- Every fibre of the angular projection is countable, being a full residue class. -/
theorem countable_preimage_coe_singleton (x : Angle) :
    ((fun s : ℝ ↦ (s : Angle)) ⁻¹' {x}).Countable := by
  refine Set.Countable.mono ?_
    (Set.countable_range fun k : ℤ ↦ x.toReal + 2 * Real.pi * (k : ℝ))
  intro y hy
  have hy' : ((y : ℝ) : Angle) = ((x.toReal : ℝ) : Angle) := by
    rw [mem_preimage, mem_singleton_iff] at hy
    rw [hy, coe_toReal]
  obtain ⟨k, hk⟩ := angle_eq_iff_two_pi_dvd_sub.mp hy'
  exact ⟨k, by linarith [hk]⟩

/-- The quotient map sends an open real interval to an open angular arc. -/
theorem isOpen_image_Ioo (a b : ℝ) :
    IsOpen ((fun t : ℝ ↦ (t : Angle)) '' Ioo a b) := by
  exact QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo

/-- The frontier of an angular arc is contained in its two endpoint angles. -/
theorem frontier_image_Ioo_subset (a b : ℝ) :
    frontier ((fun t : ℝ ↦ (t : Angle)) '' Ioo a b) ⊆
      {(a : Angle), (b : Angle)} := by
  intro x hx
  have hc : IsClosed ((fun t : ℝ ↦ (t : Angle)) '' Icc a b) :=
    (isCompact_Icc.image continuous_coe).isClosed
  have hx' : x ∈ (fun t : ℝ ↦ (t : Angle)) '' Icc a b :=
    closure_minimal (image_mono Ioo_subset_Icc_self) hc hx.1
  obtain ⟨t, ht, rfl⟩ := hx'
  have hout : (t : Angle) ∉ (fun t : ℝ ↦ (t : Angle)) '' Ioo a b := by
    simpa only [(isOpen_image_Ioo a b).interior_eq] using hx.2
  have hends : t = a ∨ t = b := by
    by_contra h
    push Not at h
    exact hout ⟨t, ⟨lt_of_le_of_ne ht.1 (Ne.symm h.1),
      lt_of_le_of_ne ht.2 h.2⟩, rfl⟩
  rcases hends with rfl | rfl <;> simp

/-- A nonempty half-open arc consists of its open arc and its terminal angle. -/
theorem image_Ioc_eq_image_Ioo_union {a b : ℝ} (hab : a < b) :
    (fun t : ℝ ↦ (t : Angle)) '' Ioc a b =
      (fun t : ℝ ↦ (t : Angle)) '' Ioo a b ∪ {(b : Angle)} := by
  rw [← Ioo_union_right hab, image_union, image_singleton]

/-- The frontier of a nonempty half-open angular arc lies in its two endpoint angles. -/
theorem frontier_image_Ioc_subset {a b : ℝ} (hab : a < b) :
    frontier ((fun t : ℝ ↦ (t : Angle)) '' Ioc a b) ⊆
      {(a : Angle), (b : Angle)} := by
  rw [image_Ioc_eq_image_Ioo_union hab]
  refine (frontier_union_subset _ _).trans ?_
  refine union_subset ?_ ?_
  · exact inter_subset_left.trans (frontier_image_Ioo_subset a b)
  · refine inter_subset_right.trans (frontier_subset_closure.trans ?_)
    simp

/-- Half-open real intervals have measurable angular images. -/
theorem measurableSet_image_Ioc [MeasurableSpace Angle] [BorelSpace Angle] (a b : ℝ) :
    MeasurableSet ((fun t : ℝ ↦ (t : Angle)) '' Ioc a b) := by
  by_cases hab : a < b
  · rw [image_Ioc_eq_image_Ioo_union hab]
    exact (isOpen_image_Ioo a b).measurableSet.union (measurableSet_singleton _)
  · simp [Ioc_eq_empty_of_le (le_of_not_gt hab)]

/-- A Borel subset of a real interval of at most one turn has a Borel angular image. -/
theorem measurableSet_image_of_subset_Ioc [MeasurableSpace Angle] [BorelSpace Angle]
    {a b : ℝ} (hab : b ≤ a + 2 * Real.pi) {E : Set ℝ} (hE : MeasurableSet E)
    (hEab : E ⊆ Ioc a b) :
    MeasurableSet ((fun t : ℝ ↦ (t : Angle)) '' E) :=
  hE.image_of_continuousOn_injOn continuous_coe.continuousOn ((injOn_coe_Ioc hab).mono hEab)

/-- The preimage of an open angular arc under the half-turn shift is the shifted arc. -/
theorem preimage_sub_pi_image_Ioo (a b : ℝ) :
    (fun t : Angle ↦ t - ((Real.pi : ℝ) : Angle)) ⁻¹'
        ((fun s : ℝ ↦ (s : Angle)) '' Ioo a b) =
      (fun s : ℝ ↦ (s : Angle)) '' Ioo (a + Real.pi) (b + Real.pi) := by
  ext x
  simp only [mem_preimage, mem_image, mem_Ioo]
  constructor
  · rintro ⟨s, hs, hsx⟩
    refine ⟨s + Real.pi, ⟨by linarith [hs.1], by linarith [hs.2]⟩, ?_⟩
    rw [coe_add, hsx]
    abel
  · rintro ⟨r, hr, hrx⟩
    refine ⟨r - Real.pi, ⟨by linarith [hr.1], by linarith [hr.2]⟩, ?_⟩
    rw [coe_sub, hrx]

/-- The terminal atom is disjoint from the open arc, even for a full turn. -/
theorem disjoint_image_Ioo_singleton {a b : ℝ} (h : b ≤ a + 2 * Real.pi) :
    Disjoint ((fun t : ℝ ↦ (t : Angle)) '' Ioo a b) {(b : Angle)} := by
  rw [Set.disjoint_singleton_right]
  rintro ⟨t, ht, heq⟩
  have htb := injOn_coe_Ioc h ⟨ht.1, ht.2.le⟩ ⟨ht.1.trans ht.2, le_rfl⟩ heq
  exact ht.2.ne htb

/-- Passing from an open arc to a half-open arc restores exactly its terminal atom. -/
theorem integral_image_Ioc [MeasurableSpace Angle] [BorelSpace Angle]
    (μ : MeasureTheory.FiniteMeasure Angle) (f : Angle →ᵇ ℝ)
    {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi) :
    (∫ x in (fun t : ℝ ↦ (t : Angle)) '' Ioc a b, f x ∂(μ : MeasureTheory.Measure Angle)) =
      (∫ x in (fun t : ℝ ↦ (t : Angle)) '' Ioo a b, f x ∂(μ : MeasureTheory.Measure Angle)) +
        (μ : MeasureTheory.Measure Angle).real {(b : Angle)} * f (b : Angle) := by
  rw [image_Ioc_eq_image_Ioo_union hab, MeasureTheory.setIntegral_union
    (disjoint_image_Ioo_singleton hturn) (measurableSet_singleton _)
    (f.integrable (μ := (μ : Measure Angle))).integrableOn
    (f.integrable (μ := (μ : Measure Angle))).integrableOn]
  rw [MeasureTheory.integral_singleton]
  rfl

/-- Weak convergence with fixed endpoint atoms preserves integrals on half-open angular arcs. -/
theorem tendsto_integral_image_Ioc_of_fixed_endpoint_atoms
    [MeasurableSpace Angle] [BorelSpace Angle]
    {ι : Type*} {F : Filter ι} {μs : ι → FiniteMeasure Angle} {μ : FiniteMeasure Angle}
    {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi)
    (hμ : Tendsto μs F (𝓝 μ))
    (ha : ∀ n, (μs n : Measure Angle) {(a : Angle)} = (μ : Measure Angle) {(a : Angle)})
    (hb : ∀ n, (μs n : Measure Angle) {(b : Angle)} = (μ : Measure Angle) {(b : Angle)})
    (f : Angle →ᵇ ℝ) :
    Tendsto (fun n ↦ ∫ x in (fun t : ℝ ↦ (t : Angle)) '' Ioc a b,
      f x ∂(μs n : Measure Angle)) F
      (𝓝 (∫ x in (fun t : ℝ ↦ (t : Angle)) '' Ioc a b, f x ∂(μ : Measure Angle))) := by
  classical
  have hatoms : ∀ n x, x ∈ ({(a : Angle), (b : Angle)} : Finset Angle) →
      (μs n : Measure Angle) {x} = (μ : Measure Angle) {x} := by
    intro n x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha n
    · exact hb n
  have hres := FiniteMeasure.tendsto_restrict_of_frontier_subset_finset
    (isOpen_image_Ioo a b).measurableSet ({(a : Angle), (b : Angle)} : Finset Angle)
    (by simpa using frontier_image_Ioo_subset a b) hμ hatoms
  have hint := FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hres f
  have hatom (n : ι) : (μs n : Measure Angle).real {(b : Angle)} =
      (μ : Measure Angle).real {(b : Angle)} := by
    exact congrArg ENNReal.toReal (hb n)
  simpa only [integral_image_Ioc _ _ hab hturn, hatom,
    FiniteMeasure.restrict_measure_eq] using
      hint.add (tendsto_const_nhds (x := (μ : Measure Angle).real {(b : Angle)} * f (b : Angle)))

/-! ### Integration over the circle of directions -/

/-- A continuous function of a direction is integrable for every finite angular measure, the
circle of directions being compact. -/
theorem integrable_of_continuous [MeasurableSpace Angle] [BorelSpace Angle] {E : Type*}
    [NormedAddCommGroup E] {μ : Measure Angle} [IsFiniteMeasure μ] {f : Angle → E}
    (hf : Continuous f) : Integrable f μ := by
  have : Fact (0 < 2 * Real.pi) := ⟨mul_pos (by norm_num) Real.pi_pos⟩
  have : CompactSpace Angle := inferInstanceAs (CompactSpace (AddCircle (2 * Real.pi)))
  exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-! ### Angular measures reading a real density -/

/-- On a real window of at most one turn, the pushforward of a weighted measure along the
angular projection gives the angular image of a measurable subset the integral of the weight
over that subset. -/
theorem map_coe_withDensity_image_eq_setLIntegral [MeasurableSpace Angle] [BorelSpace Angle]
    {ν : Measure ℝ} {w : ℝ → ENNReal} {S T : Set ℝ} {a b : ℝ}
    (hturn : b ≤ a + 2 * Real.pi) (hS : S ⊆ Ioc a b) (hT : MeasurableSet T) (hTS : T ⊆ S) :
    Measure.map (fun t : ℝ ↦ (t : Angle)) ((ν.restrict S).withDensity w)
        ((fun t : ℝ ↦ (t : Angle)) '' T) = ∫⁻ t in T, w t ∂ν := by
  have hmeas : Measurable fun t : ℝ ↦ (t : Angle) := continuous_coe.measurable
  have himage : MeasurableSet ((fun t : ℝ ↦ (t : Angle)) '' T) :=
    measurableSet_image_of_subset_Ioc hturn hT (hTS.trans hS)
  have hpre : MeasurableSet ((fun t : ℝ ↦ (t : Angle)) ⁻¹'
      ((fun t : ℝ ↦ (t : Angle)) '' T)) := himage.preimage hmeas
  have hback : (fun t : ℝ ↦ (t : Angle)) ⁻¹' ((fun t : ℝ ↦ (t : Angle)) '' T) ∩ S = T := by
    refine Subset.antisymm ?_ fun x hx ↦ ⟨mem_image_of_mem _ hx, hTS hx⟩
    rintro x ⟨⟨y, hy, hxy⟩, hxS⟩
    exact injOn_coe_Ioc hturn (hS (hTS hy)) (hS hxS) hxy ▸ hy
  rw [Measure.map_apply hmeas himage, withDensity_apply _ hpre, Measure.restrict_restrict hpre,
    hback]

/-- Two angular measures that agree on the angular image of every measurable subset of a real
window agree after restriction to that window's angular image. -/
theorem measure_restrict_image_congr [MeasurableSpace Angle] [BorelSpace Angle]
    {μ ν : Measure Angle} {J : Set ℝ} (hJ : MeasurableSet J)
    (h : ∀ T, MeasurableSet T → T ⊆ J →
      μ ((fun t : ℝ ↦ (t : Angle)) '' T) = ν ((fun t : ℝ ↦ (t : Angle)) '' T)) :
    μ.restrict ((fun t : ℝ ↦ (t : Angle)) '' J) =
      ν.restrict ((fun t : ℝ ↦ (t : Angle)) '' J) := by
  have hmeas : Measurable fun t : ℝ ↦ (t : Angle) := continuous_coe.measurable
  ext A hA
  have hpre : MeasurableSet ((fun t : ℝ ↦ (t : Angle)) ⁻¹' A) := hA.preimage hmeas
  rw [Measure.restrict_apply hA, Measure.restrict_apply hA, inter_comm,
    ← image_inter_preimage, h _ (hJ.inter hpre) inter_subset_left]

/-- Two angular measures reading extended-real weights on a real window agree after restriction
to its angular image as soon as the weights agree almost everywhere on the window. -/
theorem measure_restrict_image_congr_of_ae_eq [MeasurableSpace Angle] [BorelSpace Angle]
    {μ ν : Measure Angle} {ρ : Measure ℝ} {w w' : ℝ → ENNReal} {J : Set ℝ}
    (hJ : MeasurableSet J)
    (hμ : ∀ T, MeasurableSet T → T ⊆ J →
      μ ((fun t : ℝ ↦ (t : Angle)) '' T) = ∫⁻ t in T, w t ∂ρ)
    (hν : ∀ T, MeasurableSet T → T ⊆ J →
      ν ((fun t : ℝ ↦ (t : Angle)) '' T) = ∫⁻ t in T, w' t ∂ρ)
    (hw : ∀ᵐ t ∂ρ.restrict J, w t = w' t) :
    μ.restrict ((fun t : ℝ ↦ (t : Angle)) '' J) =
      ν.restrict ((fun t : ℝ ↦ (t : Angle)) '' J) := by
  refine measure_restrict_image_congr hJ fun T hT hTJ ↦ ?_
  rw [hμ T hT hTJ, hν T hT hTJ]
  exact lintegral_congr_ae (ae_restrict_of_ae_restrict_of_subset hTJ hw)

/-- An angular measure reading a real density on a window agrees, after restriction to the
window's angular image, with a sum of two angular measures whose densities add up to it almost
everywhere. -/
theorem measure_restrict_image_congr_add [MeasurableSpace Angle] [BorelSpace Angle]
    {μ ν₁ ν₂ : Measure Angle} {ρ : Measure ℝ} {f g h : ℝ → ℝ} {J : Set ℝ}
    (hJ : MeasurableSet J)
    (hμ : ∀ T, MeasurableSet T → T ⊆ J →
      μ ((fun t : ℝ ↦ (t : Angle)) '' T) = ∫⁻ t in T, ENNReal.ofReal (h t) ∂ρ)
    (hν₁ : ∀ T, MeasurableSet T → T ⊆ J →
      ν₁ ((fun t : ℝ ↦ (t : Angle)) '' T) = ∫⁻ t in T, ENNReal.ofReal (f t) ∂ρ)
    (hν₂ : ∀ T, MeasurableSet T → T ⊆ J →
      ν₂ ((fun t : ℝ ↦ (t : Angle)) '' T) = ∫⁻ t in T, ENNReal.ofReal (g t) ∂ρ)
    (hf : AEMeasurable f (ρ.restrict J)) (hf0 : ∀ᵐ t ∂ρ.restrict J, 0 ≤ f t)
    (hg0 : ∀ᵐ t ∂ρ.restrict J, 0 ≤ g t) (hfg : ∀ᵐ t ∂ρ.restrict J, h t = f t + g t) :
    μ.restrict ((fun t : ℝ ↦ (t : Angle)) '' J) =
      (ν₁ + ν₂).restrict ((fun t : ℝ ↦ (t : Angle)) '' J) := by
  refine measure_restrict_image_congr hJ fun T hT hTJ ↦ ?_
  have hsplit : ∀ᵐ t ∂ρ.restrict T,
      ENNReal.ofReal (h t) = ENNReal.ofReal (f t) + ENNReal.ofReal (g t) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hTJ hf0,
      ae_restrict_of_ae_restrict_of_subset hTJ hg0,
      ae_restrict_of_ae_restrict_of_subset hTJ hfg] with t h1 h2 h3
    rw [h3, ENNReal.ofReal_add h1 h2]
  have hfT : AEMeasurable (fun t ↦ ENNReal.ofReal (f t)) (ρ.restrict T) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (hf.mono_measure (Measure.restrict_mono hTJ le_rfl))
  rw [hμ T hT hTJ, Measure.add_apply, hν₁ T hT hTJ, hν₂ T hT hTJ, lintegral_congr_ae hsplit,
    lintegral_add_left' hfT]

end Real.Angle
