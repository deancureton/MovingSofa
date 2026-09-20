import MovingSofa.ForMathlib.Convex.Body.Hausdorff
import MovingSofa.ForMathlib.Convex.Support
import MovingSofa.ForMathlib.Convex.Collinear
import MovingSofa.Classical.Area
import Mathlib.Analysis.Normed.Lp.PiLp
import MovingSofa.ForMathlib.Convex.Hausdorff
import Mathlib.Analysis.Convex.Measure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.MetricSpace.Thickening
import MovingSofa.Geometry.FrameCalculus

noncomputable section

open Filter
open scoped Topology

namespace MovingSofa

def vectorSupport (S : Set Point) (u : Point) : ℝ := sSup ((fun x ↦ inner ℝ x u) '' S)

/-- Support values in a unit direction vary by at most the Hausdorff distance. -/
theorem abs_vectorSupport_sub_le_hausdorffDist {S T : Set Point}
    (hS : S.Nonempty) (hcS : IsCompact S) (hT : T.Nonempty) (hcT : IsCompact T)
    {u : Point} (hu : ‖u‖ = 1) :
    |vectorSupport S u - vectorSupport T u| ≤ Metric.hausdorffDist S T := by
  simpa only [vectorSupport, hu, mul_one] using
    hcS.abs_csSup_inner_sub_le_hausdorffDist hS hcT hT u

theorem convexBody_selection (A : Set Point) (hA : IsCompact A)
    (K : ℕ → ConvexBody Point) (hK : ∀ n, (K n : Set Point) ⊆ A) :
    ∃ (φ : ℕ → ℕ) (L : ConvexBody Point), StrictMono φ ∧
      Tendsto (fun n ↦ Metric.hausdorffDist (K (φ n) : Set Point) (L : Set Point))
        atTop (𝓝 0) := by
  let C : ℕ → TopologicalSpace.NonemptyCompacts Point := fun n ↦
    ⟨⟨(K n : Set Point), (K n).isCompact⟩, (K n).nonempty⟩
  obtain ⟨L, hLA, φ, hφ, hlim⟩ :=
    (TopologicalSpace.NonemptyCompacts.isCompact_subsets_of_isCompact hA).tendsto_subseq
      (show ∀ n, C n ∈ {L : TopologicalSpace.NonemptyCompacts Point | (L : Set Point) ⊆ A}
        from hK)
  have hconv : Convex ℝ (L : Set Point) :=
    TopologicalSpace.NonemptyCompacts.convex_of_tendsto (fun n ↦ (K (φ n)).convex) hlim
  refine ⟨φ, ⟨(L : Set Point), hconv, L.isCompact, L.nonempty⟩, hφ, ?_⟩
  simpa only [C, Function.comp_apply, TopologicalSpace.NonemptyCompacts.dist_eq,
    TopologicalSpace.NonemptyCompacts.coe_mk, TopologicalSpace.Compacts.coe_mk, ConvexBody.coe_mk] using
    (tendsto_iff_dist_tendsto_zero.mp hlim)

theorem compactSet_support_continuity (S T : Set Point)
    (hS : S.Nonempty) (hcS : IsCompact S) (hT : T.Nonempty) (hcT : IsCompact T) :
    (∀ u v : Point, ‖u‖ = 1 → ‖v‖ = 1 →
      |vectorSupport S u - vectorSupport S v| ≤ sSup (norm '' S) * ‖u - v‖) ∧
    (∀ u : Point, ‖u‖ = 1 →
      |vectorSupport S u - vectorSupport T u| ≤ Metric.hausdorffDist S T) ∧
    Continuous (fun t : Real.Angle ↦ supportValue S t) ∧
    (∀ (K : ℕ → Set Point), (∀ n, (K n).Nonempty ∧ IsCompact (K n)) →
      Tendsto (fun n ↦ Metric.hausdorffDist (K n) S) atTop (𝓝 0) →
      TendstoUniformlyOn (fun n u ↦ vectorSupport (K n) u) (vectorSupport S)
        atTop {u | ‖u‖ = 1}) := by
  constructor
  · intro u v _ _
    exact hcS.abs_csSup_inner_sub_le hS u v
  constructor
  · intro u hu
    exact abs_vectorSupport_sub_le_hausdorffDist hS hcS hT hcT hu
  constructor
  · unfold supportValue
    apply hcS.continuous_sSup
    change Continuous (fun q : Real.Angle × Point ↦ inner ℝ q.2 (normalVector q.1))
    have hn : Continuous (fun q : Real.Angle × Point ↦ normalVector q.1) := by
      let c : Real.Angle × Point → (i : Fin 2) → ℝ :=
        fun q i ↦ Fin.cases q.1.cos (fun _ ↦ q.1.sin) i
      have hc : Continuous c := by
        apply continuous_pi
        intro i
        fin_cases i
        · exact Real.Angle.continuous_cos.comp continuous_fst
        · exact Real.Angle.continuous_sin.comp continuous_fst
      have heq : (fun q : Real.Angle × Point ↦ normalVector q.1) =
          (fun q ↦ WithLp.toLp 2 (c q)) := by
        funext q
        ext i
        fin_cases i <;> rfl
      rw [heq]
      exact (PiLp.continuous_toLp (2 : ENNReal) (fun _ : Fin 2 ↦ ℝ)).comp hc
    simpa [Function.comp_def] using
      (continuous_inner (𝕜 := ℝ) (E := Point)).comp (continuous_snd.prodMk hn)
  · intro K hK hlim
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn
    intro u hu
    rw [Real.dist_eq]
    exact (abs_vectorSupport_sub_le_hausdorffDist hS hcS
      (hK n).1 (hK n).2 hu).trans_lt (by simpa [Metric.hausdorffDist_comm] using hn)

private theorem exists_inner_pos_of_eq_iInter
    (U : Set Point) (K : Set Point) (hne : K.Nonempty) (hbounded : Bornology.IsBounded K)
    (hK : K = ⋂ u ∈ U, {x | inner ℝ x u ≤ vectorSupport K u}) :
    ∀ d : Point, d ≠ 0 → ∃ u ∈ U, 0 < inner ℝ d u := by
  intro d hd
  by_contra hno
  push Not at hno
  obtain ⟨z, hz⟩ := hne
  obtain ⟨R, hR⟩ := Metric.isBounded_iff_subset_closedBall (0 : Point) |>.1 hbounded
  have hzI : z ∈ ⋂ u ∈ U, {x | inner ℝ x u ≤ vectorSupport K u} := by
    rw [← hK]
    exact hz
  have hmem : ∀ t : ℝ, 0 ≤ t → z + t • d ∈ K := by
    intro t ht
    rw [hK]
    simp only [Set.mem_iInter]
    intro u hu
    have hz' := (Set.mem_iInter.mp (Set.mem_iInter.mp hzI u) hu)
    dsimp at hz' ⊢
    rw [inner_add_left, inner_smul_left]
    change inner ℝ z u + t * inner ℝ d u ≤ vectorSupport K u
    have hdu : inner ℝ d u ≤ 0 := hno u hu
    have htd : t * inner ℝ d u ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht hdu
    nlinarith [hz', htd]
  have hnorm : ∀ t : ℝ, 0 ≤ t → ‖z + t • d‖ ≤ R := by
    intro t ht
    simpa [dist_eq_norm] using (Metric.mem_closedBall.mp (hR (hmem t ht)))
  have hd' : 0 < ‖d‖ := norm_pos_iff.mpr hd
  have hR0 : 0 ≤ R := dist_nonneg.trans (Metric.mem_closedBall.mp (hR hz))
  let t : ℝ := (R + ‖z‖ + 1) / ‖d‖
  have ht : 0 ≤ t := by dsimp [t]; exact div_nonneg (by positivity) (le_of_lt hd')
  have hn := hnorm t ht
  have hts : ‖t • d‖ = R + ‖z‖ + 1 := by
    dsimp [t]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
    exact div_mul_cancel₀ _ (ne_of_gt hd')
  have htriangle' : ‖t • d‖ ≤ ‖z + t • d‖ + ‖z‖ := by
    have h := norm_sub_le (z + t • d) z
    simpa [sub_eq_add_neg, add_assoc] using h
  rw [hts] at htriangle'
  nlinarith

private theorem ball_support_margin
    (U : Set Point) (L : Set Point) (q u : Point) (r : ℝ) (hr : 0 ≤ r)
    (hu : u ∈ U) (hunit : ‖u‖ = 1)
    (hball : Metric.closedBall q r ⊆ ⋂ u ∈ U,
      {x | inner ℝ x u ≤ vectorSupport L u}) :
    inner ℝ q u + r ≤ vectorSupport L u := by
  have hp : q + r • u ∈ Metric.closedBall q r := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    simp only [add_sub_cancel_left]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, hunit]
    simp
  have hp' := hball hp
  have hpu := (Set.mem_iInter.mp (Set.mem_iInter.mp hp' u) hu)
  dsimp at hpu
  rw [inner_add_left, inner_smul_left] at hpu
  have huu : inner ℝ u u = 1 := by
    rw [real_inner_self_eq_norm_sq, hunit]
    norm_num
  simp only [huu] at hpu
  simpa using hpu

private theorem eventually_ball_center_mem
    (U : Set Point) (q : Point) (r : ℝ) (hr : 0 < r)
    (K : ℕ → ConvexBody Point) (L : ConvexBody Point)
    (hK : ∀ n, (K n : Set Point) = ⋂ u ∈ U,
      {x | inner ℝ x u ≤ vectorSupport (K n) u})
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point) (L : Set Point))
      atTop (𝓝 0))
    (hq : ∀ u ∈ U, inner ℝ q u + r ≤ vectorSupport (L : Set Point) u)
    (hU : ∀ u ∈ U, ‖u‖ = 1) :
    ∀ᶠ n in atTop, q ∈ (K n : Set Point) := by
  filter_upwards [hlim.eventually (gt_mem_nhds hr)] with n hn
  rw [hK n]
  simp only [Set.mem_iInter]
  intro u hu
  have habs := (compactSet_support_continuity (K n : Set Point) (L : Set Point)
    (K n).nonempty (K n).isCompact L.nonempty L.isCompact).2.1 u (hU u hu)
  have hlower : vectorSupport (L : Set Point) u -
      Metric.hausdorffDist (K n : Set Point) (L : Set Point) ≤
      vectorSupport (K n : Set Point) u := by
    linarith [neg_le_of_abs_le habs]
  have hqr := hq u hu
  change inner ℝ q u ≤ vectorSupport (K n : Set Point) u
  calc
    inner ℝ q u ≤ vectorSupport (L : Set Point) u - r := by linarith
    _ ≤ vectorSupport (L : Set Point) u - Metric.hausdorffDist (K n : Set Point) L := by
      exact le_of_lt (by linarith)
    _ ≤ vectorSupport (K n : Set Point) u := hlower

private theorem ball_center_mem_limit
    (U : Set Point) (hU : ∀ u ∈ U, ‖u‖ = 1) (q : Point) (r : ℝ) (hr : 0 < r)
    (K : ℕ → ConvexBody Point) (L : ConvexBody Point)
    (hK : ∀ n, (K n : Set Point) = ⋂ u ∈ U,
      {x | inner ℝ x u ≤ vectorSupport (K n) u})
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point) (L : Set Point))
      atTop (𝓝 0))
    (hball : Metric.closedBall q r ⊆ ⋂ u ∈ U,
      {x | inner ℝ x u ≤ vectorSupport L u}) :
    q ∈ (L : Set Point) := by
  exact ConvexBody.mem_of_tendsto_hausdorffDist q K L
    (eventually_ball_center_mem U q r hr K L hK hlim
      (fun u hu ↦ ball_support_margin U L q u r hr.le hu (hU u hu) hball) hU) hlim

theorem fixedNormalBody_closed (U : Set Point) (hU : ∀ u ∈ U, ‖u‖ = 1)
    (K : ℕ → ConvexBody Point) (L : ConvexBody Point)
    (hK : ∀ n, (K n : Set Point) = ⋂ u ∈ U, {x | inner ℝ x u ≤ vectorSupport (K n) u})
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point) (L : Set Point))
      atTop (𝓝 0)) :
    (L : Set Point) = ⋂ u ∈ U, {x | inner ℝ x u ≤ vectorSupport L u} := by
  let H : Set Point := ⋂ u ∈ U, {x | inner ℝ x u ≤ vectorSupport L u}
  have hLH : (L : Set Point) ⊆ H := by
    intro x hx
    simp only [H, Set.mem_iInter, Set.mem_ofPred_eq]
    intro u hu
    exact le_csSup (L.isCompact.bddAbove_image
      (continuous_inner.comp (continuous_id.prodMk continuous_const)).continuousOn)
      ⟨x, hx, rfl⟩
  have hH : Convex ℝ H := by
    intro x hx y hy a b ha hb hab
    simp only [H, Set.mem_iInter, Set.mem_ofPred_eq] at hx hy ⊢
    intro u hu
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    calc
      a * inner ℝ x u + b * inner ℝ y u ≤
          a * vectorSupport L u + b * vectorSupport L u :=
        add_le_add (mul_le_mul_of_nonneg_left (hx u hu) ha)
          (mul_le_mul_of_nonneg_left (hy u hu) hb)
      _ = vectorSupport L u := by rw [← add_mul, hab, one_mul]
  have hint : interior H ⊆ (L : Set Point) := by
    intro x hx
    obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
      (mem_interior_iff_mem_nhds.mp hx)
    exact ball_center_mem_limit U hU x r hr K L hK hlim hball
  apply Set.Subset.antisymm hLH
  rcases (interior H).eq_empty_or_nonempty with hempty | hnonempty
  · have hcol : Collinear ℝ H := hH.collinear_of_interior_eq_empty (by
      simp [Point, finrank_euclideanSpace]) hempty
    intro p hp
    obtain ⟨a, ha⟩ := L.nonempty
    by_cases hpa : p = a
    · simpa only [hpa] using ha
    obtain ⟨u, hu, hpos⟩ := exists_inner_pos_of_eq_iInter U (K 0) (K 0).nonempty
      (K 0).isCompact.isBounded (hK 0)
      (p - a) (sub_ne_zero.mpr hpa)
    have hmax : ∃ x ∈ (L : Set Point), vectorSupport L u = inner ℝ x u ∧
        ∀ y ∈ (L : Set Point), inner ℝ y u ≤ inner ℝ x u := by
      simpa only [vectorSupport, Function.comp_apply, id_eq] using
        L.isCompact.exists_sSup_image_eq_and_ge (α := ℝ) (β := Point)
          (f := fun x : Point ↦ inner ℝ x u) L.nonempty
          (continuous_inner.comp (continuous_id.prodMk continuous_const)).continuousOn
    obtain ⟨x, hx, hxu, _⟩ := hmax
    have hle : inner ℝ p u ≤ inner ℝ x u := by
      rw [← hxu]
      exact Set.mem_iInter.mp (Set.mem_iInter.mp hp u) hu
    have hsegment := hcol.mem_segment_of_apply_le (hLH ha) hp (hLH hx)
      (innerSL ℝ u).toLinearMap (by change 0 < inner ℝ u (p - a); rwa [real_inner_comm])
      (by change inner ℝ u p ≤ inner ℝ u x; simpa only [real_inner_comm u] using hle)
    exact L.convex.segment_subset ha hx hsegment
  · have hclosure : closure (interior H) = closure H :=
      hH.closure_interior_eq_closure_of_nonempty_interior hnonempty
    exact subset_closure.trans (hclosure ▸ L.isClosed.closure_subset_iff.mpr hint)

theorem convexArea_hausdorff_continuity (K : ℕ → ConvexBody Point) (L : ConvexBody Point)
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point) (L : Set Point))
      atTop (𝓝 0)) :
    Tendsto (fun n ↦ ClassicalResults.area (K n)) atTop (𝓝 (ClassicalResults.area L)) := by
  let U : Set Point := {u | ‖u‖ = 1}
  have hrepK : ∀ n, (K n : Set Point) = ⋂ u ∈ U,
      {x | inner ℝ x u ≤ vectorSupport (K n) u} := by
    intro n
    simpa only [U, vectorSupport] using ConvexBody.eq_iInter_halfSpaces (K n)
  have hrepL : (L : Set Point) = ⋂ u ∈ U,
      {x | inner ℝ x u ≤ vectorSupport L u} := by
    simpa only [U, vectorSupport] using ConvexBody.eq_iInter_halfSpaces L
  obtain ⟨R, hR, hcompact⟩ := L.isCompact.exists_isCompact_cthickening
  let C : Set Point := Metric.cthickening R (L : Set Point)
  have hsubset : ∀ᶠ n in atTop, (K n : Set Point) ⊆ C := by
    filter_upwards [hlim.eventually (gt_mem_nhds hR)] with n hn p hp
    obtain ⟨q, hq, hpq⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt hp hn
      (Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
        (K n).nonempty L.nonempty (K n).isCompact.isBounded L.isCompact.isBounded)
    exact Metric.mem_cthickening_of_dist_le p q R L hq hpq.le
  have hpointwise : ∀ p ∉ frontier (L : Set Point),
      Tendsto (fun n ↦ (K n : Set Point).indicator (fun _ ↦ (1 : ℝ)) p) atTop
        (𝓝 ((L : Set Point).indicator (fun _ ↦ (1 : ℝ)) p)) := by
    intro p hpfrontier
    by_cases hpL : p ∈ (L : Set Point)
    · have hpint : p ∈ interior (L : Set Point) := by
        by_contra hp
        exact hpfrontier ((mem_frontier_iff_notMem_interior hpL).mpr hp)
      obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
        (mem_interior_iff_mem_nhds.mp hpint)
      have hmargin : ∀ u ∈ U, inner ℝ p u + r ≤ vectorSupport L u := by
        intro u hu
        rw [hrepL] at hball
        exact ball_support_margin U L p u r hr.le hu hu hball
      have hev := eventually_ball_center_mem U p r hr K L hrepK hlim hmargin
        (fun _ hu ↦ hu)
      apply tendsto_nhds_of_eventually_eq
      filter_upwards [hev] with n hn
      simp [hn, hpL]
    · have hdist : 0 < Metric.infDist p (L : Set Point) := by
        exact (Metric.infDist_pos_iff_notMem_closure L.nonempty).mp (by
          rwa [L.isClosed.closure_eq])
      have hev : ∀ᶠ n in atTop, p ∉ (K n : Set Point) := by
        filter_upwards [hlim.eventually (gt_mem_nhds hdist)] with n hn hpn
        have hle := Metric.infDist_le_hausdorffDist_of_mem hpn
          (Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
            (K n).nonempty L.nonempty (K n).isCompact.isBounded L.isCompact.isBounded)
        linarith
      apply tendsto_nhds_of_eventually_eq
      filter_upwards [hev] with n hn
      simp [hn, hpL]
  have hfrontier : MeasureTheory.volume (frontier (L : Set Point)) = 0 :=
    L.convex.addHaar_frontier MeasureTheory.volume
  have hmeas : ∀ n, MeasurableSet (K n : Set Point) := fun n ↦ (K n).isCompact.measurableSet
  have hCmeas : MeasurableSet C := hcompact.measurableSet
  have hCint : MeasureTheory.Integrable (C.indicator fun _ ↦ (1 : ℝ)) := by
    exact (MeasureTheory.integrableOn_const hcompact.measure_lt_top.ne).integrable_indicator hCmeas
  have htendsto := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := MeasureTheory.volume)
    (F := fun n ↦ (K n : Set Point).indicator fun _ ↦ (1 : ℝ))
    (f := (L : Set Point).indicator fun _ ↦ (1 : ℝ))
    (C.indicator fun _ ↦ (1 : ℝ))
    (Filter.Eventually.of_forall fun n ↦
      (measurable_const.indicator (hmeas n)).aestronglyMeasurable)
    (by
      filter_upwards [hsubset] with n hn
      filter_upwards [] with p
      by_cases hp : p ∈ (K n : Set Point)
      · have hpC := hn hp
        simp [hp, hpC]
      · by_cases hpC : p ∈ C <;> simp [hp, hpC])
    hCint
    (by
      filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hfrontier] with p hp
      exact hpointwise p hp)
  have heqK : ∀ n, (∫ p, (K n : Set Point).indicator (fun _ ↦ (1 : ℝ)) p) =
      MeasureTheory.volume.real (K n : Set Point) := by
    intro n
    change (∫ p, (K n : Set Point).indicator 1 p) = _
    exact MeasureTheory.integral_indicator_one (μ := MeasureTheory.volume) (hmeas n)
  have heqL : (∫ p, (L : Set Point).indicator (fun _ ↦ (1 : ℝ)) p) =
      MeasureTheory.volume.real (L : Set Point) := by
    change (∫ p, (L : Set Point).indicator 1 p) = _
    exact MeasureTheory.integral_indicator_one (μ := MeasureTheory.volume)
      L.isCompact.measurableSet
  simp_rw [heqK] at htendsto
  rw [heqL] at htendsto
  simpa [ClassicalResults.area, MeasureTheory.Measure.real] using htendsto

/-- The support function of a convex body is continuous in the normal direction. -/
theorem continuous_supportValue (K : ConvexBody Point) :
    Continuous fun t : Real.Angle ↦ supportValue (K : Set Point) t :=
  (compactSet_support_continuity K K K.nonempty K.isCompact K.nonempty K.isCompact).2.2.1

theorem continuous_supportValue_real (K : ConvexBody Point) :
    Continuous (fun t : ℝ ↦ supportValue K (t : Real.Angle)) :=
  (continuous_supportValue K).comp Real.Angle.continuous_coe

/-- Support values of a nonempty compact set are Lipschitz in the real angle, with the largest
norm of a point of the set as Lipschitz constant. -/
theorem abs_supportValue_sub_le_of_isCompact {s : Set Point} (hne : s.Nonempty)
    (hc : IsCompact s) (x y : ℝ) :
    |supportValue s (x : Real.Angle) - supportValue s (y : Real.Angle)| ≤
      sSup (norm '' s) * |x - y| := by
  have hdir := (compactSet_support_continuity s s hne hc hne hc).1
    (normalVector (x : Real.Angle)) (normalVector (y : Real.Angle))
    (norm_normalVector_real x) (norm_normalVector_real y)
  have hframe : ‖normalVector (x : Real.Angle) - normalVector (y : Real.Angle)‖ ≤ |x - y| := by
    simpa [dist_eq_norm, Real.dist_eq] using lipschitzWith_normalVector_real.dist_le_mul x y
  have h0 : 0 ≤ sSup (norm '' s) :=
    Real.sSup_nonneg (by rintro _ ⟨p, -, rfl⟩; exact norm_nonneg p)
  exact hdir.trans (mul_le_mul_of_nonneg_left hframe h0)

end MovingSofa
