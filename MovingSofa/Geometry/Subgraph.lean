import MovingSofa.Geometry.Plane
import Mathlib.Topology.Instances.Matrix

/-!
# The planar region under the graph of a function

For `a b : ℝ` and `f : ℝ → ℝ` this file describes the three planar regions between the
horizontal axis and the graph of `f` over `[a, b]`: `closedSubgraph`, which contains both the
base segment and the graph, `strictSubgraph`, which contains the base but not the graph, and
`openSubgraph`, which contains neither.

For a function continuous on `[a, b]`, vanishing at `a` and `b` and positive in between, the
closed region is the closure of either smaller region (`closure_openSubgraph`,
`closure_strictSubgraph`) and the open region is its interior (`interior_closedSubgraph`).
-/

noncomputable section

namespace MovingSofa

/-- A planar point is recovered from its two coordinates. -/
theorem Point.eq_vecNotation (z : Point) : z = !₂[z 0, z 1] := by
  ext i
  fin_cases i <;> simp

/-- The closed region between the base and the graph of `f` over `[a, b]`. -/
def closedSubgraph (a b : ℝ) (f : ℝ → ℝ) : Set Point :=
  {q | a ≤ q 0 ∧ q 0 ≤ b ∧ 0 ≤ q 1 ∧ q 1 ≤ f (q 0)}

/-- The region under the graph of `f` over `[a, b]`, including the base but not the graph. -/
def strictSubgraph (a b : ℝ) (f : ℝ → ℝ) : Set Point :=
  {q | a ≤ q 0 ∧ q 0 ≤ b ∧ 0 ≤ q 1 ∧ q 1 < f (q 0)}

/-- The open region strictly between the base and the graph of `f` over `(a, b)`. -/
def openSubgraph (a b : ℝ) (f : ℝ → ℝ) : Set Point :=
  {q | a < q 0 ∧ q 0 < b ∧ 0 < q 1 ∧ q 1 < f (q 0)}

section Subgraph

variable {a b : ℝ} {f : ℝ → ℝ}

/-- The open subgraph omits the base, which the strict subgraph contains. -/
theorem openSubgraph_subset_strictSubgraph : openSubgraph a b f ⊆ strictSubgraph a b f :=
  fun _ h ↦ ⟨h.1.le, h.2.1.le, h.2.2.1.le, h.2.2.2⟩

/-- The strict subgraph omits the graph, which the closed subgraph contains. -/
theorem strictSubgraph_subset_closedSubgraph : strictSubgraph a b f ⊆ closedSubgraph a b f :=
  fun _ h ↦ ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.le⟩

/-- The open subgraph is contained in the closed one. -/
theorem openSubgraph_subset_closedSubgraph : openSubgraph a b f ⊆ closedSubgraph a b f :=
  openSubgraph_subset_strictSubgraph.trans strictSubgraph_subset_closedSubgraph

/-- The vertical line through a fixed horizontal coordinate is continuous. -/
private theorem continuous_verticalLine (c : ℝ) :
    Continuous fun y : ℝ ↦ (!₂[c, y] : Point) :=
  (PiLp.continuous_toLp (2 : ENNReal) fun _ : Fin 2 ↦ ℝ).comp
    (continuous_const.matrixVecCons (continuous_id.matrixVecCons continuous_const))

/-- The closed subgraph of a function continuous on the base interval is closed. -/
theorem isClosed_closedSubgraph (hf : ContinuousOn f (Set.Icc a b)) :
    IsClosed (closedSubgraph a b f) := by
  have hc0 : Continuous fun q : Point ↦ q 0 := PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 0
  have hc1 : Continuous fun q : Point ↦ q 1 := PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 1
  have hSclosed : IsClosed {q : Point | q 0 ∈ Set.Icc a b} := isClosed_Icc.preimage hc0
  have hgS : ContinuousOn (fun q : Point ↦ f (q 0) - q 1) {q : Point | q 0 ∈ Set.Icc a b} :=
    (hf.comp hc0.continuousOn fun q hq ↦ hq).sub hc1.continuousOn
  have hone := hgS.preimage_isClosed_of_isClosed hSclosed (isClosed_Ici (a := (0 : ℝ)))
  have htwo : IsClosed {q : Point | 0 ≤ q 1} := isClosed_Ici.preimage hc1
  have hsplit : closedSubgraph a b f = ({q : Point | q 0 ∈ Set.Icc a b} ∩
      (fun q : Point ↦ f (q 0) - q 1) ⁻¹' Set.Ici 0) ∩ {q : Point | 0 ≤ q 1} := by
    ext q
    simp only [closedSubgraph, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Icc,
      Set.mem_preimage, Set.mem_Ici, sub_nonneg]
    tauto
  rw [hsplit]
  exact hone.inter htwo

/-- The open subgraph of a function continuous on the base interval is open. -/
theorem isOpen_openSubgraph (hf : ContinuousOn f (Set.Icc a b)) :
    IsOpen (openSubgraph a b f) := by
  have hc0 : Continuous fun q : Point ↦ q 0 := PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 0
  have hc1 : Continuous fun q : Point ↦ q 1 := PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 1
  rw [isOpen_iff_mem_nhds]
  rintro p ⟨h1, h2, h3, h4⟩
  have hfat : ContinuousAt f (p 0) :=
    (hf.mono Set.Ioo_subset_Icc_self).continuousAt (Ioo_mem_nhds h1 h2)
  have hgap : ContinuousAt (fun q : Point ↦ f (q 0) - q 1) p :=
    (ContinuousAt.comp (g := f) (f := fun q : Point ↦ q 0) (x := p) hfat
      hc0.continuousAt).sub hc1.continuousAt
  filter_upwards [hc0.continuousAt (isOpen_Ioo.mem_nhds (⟨h1, h2⟩ : p 0 ∈ Set.Ioo a b)),
    hc1.continuousAt (isOpen_Ioi.mem_nhds (show p 1 ∈ Set.Ioi (0 : ℝ) from h3)),
    hgap (isOpen_Ioi.mem_nhds (show f (p 0) - p 1 ∈ Set.Ioi (0 : ℝ) from sub_pos.mpr h4))]
    with q hq1 hq2 hq3
  exact ⟨hq1.1, hq1.2, hq2, by simpa using sub_pos.mp hq3⟩

/-- The closed subgraph is the closure of the open one: interior graph points are limits from
below, base points at interior horizontal coordinates are limits from above, and the two
corners are limits of half-height points over the open base interval. -/
theorem closure_openSubgraph (hab : a < b) (hf : ContinuousOn f (Set.Icc a b))
    (ha : f a = 0) (hb : f b = 0) (hpos : ∀ x ∈ Set.Ioo a b, 0 < f x) :
    closure (openSubgraph a b f) = closedSubgraph a b f := by
  refine Set.Subset.antisymm ((isClosed_closedSubgraph hf).closure_subset_iff.mpr ?_) ?_
  · rintro q ⟨h1, h2, h3, h4⟩
    exact ⟨h1.le, h2.le, h3.le, h4.le⟩
  · have hF : ContinuousOn (fun c ↦ (!₂[c, f c / 2] : Point)) (Set.Icc a b) :=
      (PiLp.continuous_toLp (2 : ENNReal) fun _ : Fin 2 ↦ ℝ).comp_continuousOn
        (continuous_id.continuousOn.matrixVecCons
          ((hf.div_const 2).matrixVecCons continuousOn_const))
    have hFsub : (fun c ↦ (!₂[c, f c / 2] : Point)) '' Set.Ioo a b ⊆ openSubgraph a b f := by
      rintro _ ⟨c, hc, rfl⟩
      have hfc := hpos c hc
      exact ⟨by simpa using hc.1, by simpa using hc.2, by simpa using by linarith,
        by simpa using by linarith⟩
    have hcl : closure (Set.Ioo a b) = Set.Icc a b := closure_Ioo hab.ne
    have hF' : ContinuousOn (fun c ↦ (!₂[c, f c / 2] : Point)) (closure (Set.Ioo a b)) := by
      rw [hcl]; exact hF
    have hcorner : ∀ c ∈ Set.Icc a b, (!₂[c, f c / 2] : Point) ∈ closure (openSubgraph a b f) :=
      fun c hc ↦ closure_mono hFsub (hF'.image_closure ⟨c, by rw [hcl]; exact hc, rfl⟩)
    rintro q ⟨h1, h2, h3, h4⟩
    rcases eq_or_lt_of_le h1 with hqa | hqa
    · have : q 1 = 0 := le_antisymm (by rw [← hqa, ha] at h4; exact h4) h3
      have hq : q = !₂[a, f a / 2] := by
        rw [Point.eq_vecNotation q, ← hqa, this, ha]
        norm_num
      rw [hq]
      exact hcorner a ⟨le_rfl, hab.le⟩
    rcases eq_or_lt_of_le h2 with hqb | hqb
    · have : q 1 = 0 := le_antisymm (by rw [hqb, hb] at h4; exact h4) h3
      have hq : q = !₂[b, f b / 2] := by
        rw [Point.eq_vecNotation q, hqb, this, hb]
        norm_num
      rw [hq]
      exact hcorner b ⟨hab.le, le_rfl⟩
    · have hfc : 0 < f (q 0) := hpos _ ⟨hqa, hqb⟩
      have hsub : (fun y : ℝ ↦ (!₂[q 0, y] : Point)) '' Set.Ioo 0 (f (q 0)) ⊆
          openSubgraph a b f := by
        rintro _ ⟨y, hy, rfl⟩
        exact ⟨by simpa using hqa, by simpa using hqb, by simpa using hy.1,
          by simpa using hy.2⟩
      refine closure_mono hsub ?_
      have := image_closure_subset_closure_image (continuous_verticalLine (q 0))
        (s := Set.Ioo 0 (f (q 0)))
        ⟨q 1, by rw [closure_Ioo hfc.ne]; exact ⟨h3, h4⟩, rfl⟩
      have heq : (!₂[q 0, q 1] : Point) = q := (Point.eq_vecNotation q).symm
      simpa only [heq] using this

/-- A point of the closed subgraph which is not in the open one lies on the base or on the
graph, hence is a limit of points outside the closed subgraph. -/
private theorem mem_closure_compl_closedSubgraph (ha : f a = 0) (hb : f b = 0)
    {q : Point} (hq : q ∈ closedSubgraph a b f)
    (hq' : q ∉ openSubgraph a b f) : q ∈ closure (closedSubgraph a b f)ᶜ := by
  obtain ⟨h1, h2, h3, h4⟩ := hq
  have hbelow : q 1 = 0 → q ∈ closure (closedSubgraph a b f)ᶜ := by
    intro hz
    have hsub : (fun y : ℝ ↦ (!₂[q 0, y] : Point)) '' Set.Iio 0 ⊆
        (closedSubgraph a b f)ᶜ := by
      rintro _ ⟨y, hy, rfl⟩
      intro hmem
      have h := hmem.2.2.1
      simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one] at h
      exact absurd h (not_le.mpr hy)
    refine closure_mono hsub ?_
    have := image_closure_subset_closure_image (continuous_verticalLine (q 0)) (s := Set.Iio 0)
      ⟨q 1, by rw [closure_Iio]; exact hz.le, rfl⟩
    have heq : (!₂[q 0, q 1] : Point) = q := (Point.eq_vecNotation q).symm
    simpa only [heq] using this
  rcases eq_or_lt_of_le h3 with hz | hz
  · exact hbelow hz.symm
  rcases eq_or_lt_of_le h4 with htop | htop
  · -- the point sits on the graph, which is strictly above the base here
    have hfpos : 0 < f (q 0) := htop ▸ hz
    have hsub : (fun y : ℝ ↦ (!₂[q 0, y] : Point)) '' Set.Ioi (f (q 0)) ⊆
        (closedSubgraph a b f)ᶜ := by
      rintro _ ⟨y, hy, rfl⟩
      intro hmem
      have h := hmem.2.2.2
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h
      exact absurd h (not_le.mpr hy)
    refine closure_mono hsub ?_
    have := image_closure_subset_closure_image (continuous_verticalLine (q 0))
      (s := Set.Ioi (f (q 0))) ⟨q 1, by rw [closure_Ioi]; exact htop.ge, rfl⟩
    have heq : (!₂[q 0, q 1] : Point) = q := (Point.eq_vecNotation q).symm
    simpa only [heq] using this
  · -- strictly between base and graph: the horizontal coordinate must be interior
    exfalso
    have hfpos : 0 < f (q 0) := hz.trans htop
    have hqa : a < q 0 := by
      rcases eq_or_lt_of_le h1 with h | h
      · rw [← h, ha] at hfpos; exact absurd hfpos (lt_irrefl 0)
      · exact h
    have hqb : q 0 < b := by
      rcases eq_or_lt_of_le h2 with h | h
      · rw [h, hb] at hfpos; exact absurd hfpos (lt_irrefl 0)
      · exact h
    exact hq' ⟨hqa, hqb, hz, htop⟩

/-- The open subgraph is the interior of the closed one. -/
theorem interior_closedSubgraph (hf : ContinuousOn f (Set.Icc a b))
    (ha : f a = 0) (hb : f b = 0) :
    interior (closedSubgraph a b f) = openSubgraph a b f := by
  refine Set.Subset.antisymm ?_ (interior_maximal openSubgraph_subset_closedSubgraph
    (isOpen_openSubgraph hf))
  intro q hq
  by_contra hqU
  have h2 := mem_closure_compl_closedSubgraph ha hb (interior_subset hq) hqU
  rw [closure_compl] at h2
  exact h2 hq

/-- The closed subgraph is also the closure of the strict subgraph. -/
theorem closure_strictSubgraph (hab : a < b) (hf : ContinuousOn f (Set.Icc a b))
    (ha : f a = 0) (hb : f b = 0) (hpos : ∀ x ∈ Set.Ioo a b, 0 < f x) :
    closure (strictSubgraph a b f) = closedSubgraph a b f := by
  refine Set.Subset.antisymm
    ((isClosed_closedSubgraph hf).closure_subset_iff.mpr
      strictSubgraph_subset_closedSubgraph) ?_
  rw [← closure_openSubgraph hab hf ha hb hpos]
  exact closure_mono openSubgraph_subset_strictSubgraph

end Subgraph

end MovingSofa
