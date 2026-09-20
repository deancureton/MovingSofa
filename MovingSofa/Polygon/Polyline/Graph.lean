import MovingSofa.Polygon.Polyline.Basic
import MovingSofa.Geometry.Frame
import Mathlib.Data.Finset.Sort

noncomputable section

namespace MovingSofa

/-- The point on the graph of a real-valued function above a given abscissa. -/
def pointOnGraph (f : ℝ → ℝ) (x : ℝ) : Point := !₂[x, f x]

/-- Evaluation of the affine function with slope-intercept pair `c`. -/
def affineValue (c : ℝ × ℝ) (x : ℝ) : ℝ := c.1 * x + c.2

/-- An affine real-valued function is continuous. -/
theorem continuous_affineValue (c : ℝ × ℝ) : Continuous (affineValue c) := by
  unfold affineValue
  fun_prop

private def affineCrossings (L : Finset (ℝ × ℝ)) : Set ℝ :=
  ⋃ c ∈ L, ⋃ d ∈ L.erase c, {x | affineValue c x = affineValue d x}

private theorem finite_affineValue_eq_of_ne {c d : ℝ × ℝ} (hcd : c ≠ d) :
    {x | affineValue c x = affineValue d x}.Finite := by
  apply Set.Subsingleton.finite
  intro x hx y hy
  simp only [Set.mem_ofPred_eq, affineValue] at hx hy
  by_cases hm : c.1 = d.1
  · rw [hm] at hx
    have hb : c.2 = d.2 := by linarith
    exact (hcd (Prod.ext hm hb)).elim
  · have hs : c.1 - d.1 ≠ 0 := sub_ne_zero.mpr hm
    have hprod : (c.1 - d.1) * (x - y) = 0 := by nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hs)

private theorem finite_affineCrossings (L : Finset (ℝ × ℝ)) :
    (affineCrossings L).Finite := by
  apply L.finite_toSet.biUnion
  intro c hc
  apply (L.erase c).finite_toSet.biUnion
  intro d hd
  exact finite_affineValue_eq_of_ne (Finset.ne_of_mem_erase hd).symm

@[simp] theorem pointOnGraph_apply_zero (f : ℝ → ℝ) (x : ℝ) :
    pointOnGraph f x 0 = x := by
  rfl

@[simp] theorem pointOnGraph_apply_one (f : ℝ → ℝ) (x : ℝ) :
    pointOnGraph f x 1 = f x := by
  rfl

/-- The closed vertical epigraph of a real-valued function. -/
def verticalEpigraph (f : ℝ → ℝ) : Set Point :=
  {p | f (p 0) ≤ p 1}

/-- A continuous function has a closed vertical epigraph. -/
theorem isClosed_verticalEpigraph {f : ℝ → ℝ} (hf : Continuous f) :
    IsClosed (verticalEpigraph f) := by
  exact isClosed_le
    (hf.comp (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 0))
    (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 1)

private theorem pointOnGraph_not_mem_interior_verticalEpigraph
    (f : ℝ → ℝ) (x : ℝ) :
    pointOnGraph f x ∉ interior (verticalEpigraph f) := by
  intro hx
  let q : ℕ → Point := fun n ↦ !₂[x, f x - (1 : ℝ) / (n + 1)]
  have hq : Filter.Tendsto q Filter.atTop (nhds (pointOnGraph f x)) := by
    apply (PiLp.homeomorph 2 (fun _ : Fin 2 ↦ ℝ)).isInducing.tendsto_nhds_iff.mpr
    apply tendsto_pi_nhds.mpr
    intro i
    fin_cases i
    · change Filter.Tendsto (fun _ : ℕ ↦ x) Filter.atTop (nhds x)
      exact tendsto_const_nhds
    · change Filter.Tendsto (fun n : ℕ ↦ f x - (1 : ℝ) / (n + 1))
        Filter.atTop (nhds (f x))
      simpa using (tendsto_const_nhds.sub
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hev : ∀ᶠ n in Filter.atTop, q n ∈ interior (verticalEpigraph f) :=
    hq (isOpen_interior.mem_nhds hx)
  obtain ⟨n, hn⟩ := hev.exists
  have hn' := interior_subset hn
  change f x ≤ f x - (1 : ℝ) / (n + 1) at hn'
  have : 0 < (1 : ℝ) / (n + 1) := by positivity
  linarith

/-- The frontier of a continuous vertical epigraph is its graph. -/
theorem frontier_verticalEpigraph {f : ℝ → ℝ} (hf : Continuous f) :
    frontier (verticalEpigraph f) = Set.range (pointOnGraph f) := by
  have hclosed := isClosed_verticalEpigraph hf
  ext p
  constructor
  · intro hp
    have hpE : p ∈ verticalEpigraph f := by
      exact hclosed.closure_eq ▸ frontier_subset_closure hp
    have hpNotInt : p ∉ interior (verticalEpigraph f) :=
      (mem_frontier_iff_notMem_interior hpE).mp hp
    have heq : f (p 0) = p 1 := by
      apply le_antisymm hpE
      apply le_of_not_gt
      intro hlt
      apply hpNotInt
      have hopen : IsOpen {q : Point | f (q 0) < q 1} :=
        isOpen_lt
          (hf.comp (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 0))
          (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 1)
      exact interior_maximal (fun q hq ↦ by
        change f (q 0) ≤ q 1
        exact hq.le) hopen hlt
    refine ⟨p 0, ?_⟩
    ext i
    fin_cases i
    · simp [pointOnGraph]
    · simpa [pointOnGraph] using heq
  · rintro ⟨x, rfl⟩
    apply (mem_frontier_iff_notMem_interior (s := verticalEpigraph f)
      (x := pointOnGraph f x) (by
        change f x ≤ f x
        exact le_rfl)).mpr
    exact pointOnGraph_not_mem_interior_verticalEpigraph f x

private def graphPolyline (n : ℕ) (x : Fin (n + 1) → ℝ)
    (hx : StrictMono x) (f : ℝ → ℝ) : XMonotonePolylineData where
  edges := n
  vertices i := pointOnGraph f (x i)
  increasing := by
    simpa only [pointOnGraph_apply_zero] using hx

@[simp] private theorem graphPolyline_vertices (n : ℕ) (x : Fin (n + 1) → ℝ)
    (hx : StrictMono x) (f : ℝ → ℝ) (i : Fin (n + 1)) :
    (graphPolyline n x hx f).vertices i = pointOnGraph f (x i) := by
  rfl

private theorem segment_pointOnGraph_affine {f : ℝ → ℝ} {m c a b : ℝ}
    (hab : a ≤ b) (hf : ∀ z ∈ Set.Icc a b, f z = m * z + c) :
    segment ℝ (pointOnGraph f a) (pointOnGraph f b) =
      pointOnGraph f '' Set.Icc a b := by
  ext p
  constructor
  · rintro ⟨u, v, hu, hv, huv, rfl⟩
    let z := u * a + v * b
    have hz : z ∈ Set.Icc a b := by
      constructor
      · calc
          a = (u + v) * a := by rw [huv]; ring
          _ = u * a + v * a := by ring
          _ ≤ u * a + v * b := add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hab hv)
      · calc
          u * a + v * b ≤ u * b + v * b :=
            add_le_add (mul_le_mul_of_nonneg_left hab hu) (le_refl _)
          _ = (u + v) * b := by ring
          _ = b := by rw [huv]; ring
    refine ⟨z, hz, ?_⟩
    have hfa := hf a ⟨le_rfl, hab⟩
    have hfb := hf b ⟨hab, le_rfl⟩
    have hfz := hf z hz
    ext i
    fin_cases i
    · simp [pointOnGraph, z]
    · simp [pointOnGraph, hfz, hfa, hfb, z]
      calc
        m * (u * a + v * b) + c =
            u * (m * a) + v * (m * b) + (u + v) * c := by rw [huv]; ring
        _ = u * (m * a + c) + v * (m * b + c) := by ring
  · rintro ⟨z, hz, rfl⟩
    by_cases hab' : a = b
    · subst b
      have : z = a := by exact le_antisymm hz.2 hz.1
      subst z
      simp
    · have hlt : a < b := lt_of_le_of_ne hab hab'
      let u := (b - z) / (b - a)
      let v := (z - a) / (b - a)
      have hden : 0 < b - a := sub_pos.mpr hlt
      have hu : 0 ≤ u := div_nonneg (sub_nonneg.mpr hz.2) hden.le
      have hv : 0 ≤ v := div_nonneg (sub_nonneg.mpr hz.1) hden.le
      have huv : u + v = 1 := by
        dsimp [u, v]
        field_simp
        ring
      refine ⟨u, v, hu, hv, huv, ?_⟩
      have hfa := hf a ⟨le_rfl, hab⟩
      have hfb := hf b ⟨hab, le_rfl⟩
      have hfz := hf z hz
      ext i
      fin_cases i
      · simp [pointOnGraph]
        dsimp [u, v]
        field_simp
        ring
      · simp [pointOnGraph, hfz, hfa, hfb]
        dsimp [u, v]
        field_simp
        ring

/-- A graph segment of slope `m` is orthogonal to each normal annihilating `(1,m)`. -/
theorem inner_pointOnGraph_sub_normalVector_eq_zero {f : ℝ → ℝ}
    {m c a b t : ℝ}
    (hf : Set.EqOn f (fun x ↦ m * x + c) (Set.Icc a b))
    (hab : a ≤ b) (horth : Real.cos t + m * Real.sin t = 0) :
    inner ℝ (pointOnGraph f b - pointOnGraph f a)
      (normalVector (t : Real.Angle)) = 0 := by
  have hfa := hf ⟨le_rfl, hab⟩
  have hfb := hf ⟨hab, le_rfl⟩
  simp [pointOnGraph, normalVector, frame, PiLp.inner_apply, hfa, hfb]
  nlinarith

private theorem graphPolyline_carrier_eq_image_Icc {n : ℕ} {x : Fin (n + 1) → ℝ}
    (hx : StrictMono x) {f : ℝ → ℝ}
    (hpiece : ∀ i : Fin n, ∃ m c : ℝ, ∀ z ∈ Set.Icc (x i.castSucc) (x i.succ),
      f z = m * z + c)
    (hcover : Set.Icc (x 0) (x (Fin.last n)) =
      ⋃ i : Fin n, Set.Icc (x i.castSucc) (x i.succ)) :
    (graphPolyline n x hx f).carrier =
      pointOnGraph f '' Set.Icc (x 0) (x (Fin.last n)) := by
  rw [hcover, Set.image_iUnion]
  apply Set.iUnion_congr
  intro i
  obtain ⟨m, c, hi⟩ := hpiece i
  exact segment_pointOnGraph_affine (hx i.castSucc_lt_succ).le hi

private theorem iUnion_Icc_fin {n : ℕ} (hn : 0 < n) {x : Fin (n + 1) → ℝ}
    (hx : StrictMono x) :
    Set.Icc (x 0) (x (Fin.last n)) =
      ⋃ i : Fin n, Set.Icc (x i.castSucc) (x i.succ) := by
  induction n with
  | zero => simp at hn
  | succ n ih =>
      by_cases hn0 : n = 0
      · subst n
        ext z
        constructor
        · intro hz
          exact Set.mem_iUnion.mpr ⟨0, by simpa using hz⟩
        · intro hz
          obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
          fin_cases i
          simpa using hi
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
        let y : Fin (n + 1) → ℝ := fun i ↦ x i.castSucc
        have hy : StrictMono y := hx.comp Fin.strictMono_castSucc
        have hprefix := ih hnpos hy
        have hprefix' : Set.Icc (x 0) (x (Fin.last n).castSucc) =
            ⋃ i : Fin n, Set.Icc (x i.castSucc.castSucc) (x i.succ.castSucc) := by
          simpa [y] using hprefix
        have hprefix'' : Set.Icc (x 0) (x (Fin.last n).castSucc) =
            Set.iUnion ((fun i : Fin (n + 1) ↦
              Set.Icc (x i.castSucc) (x i.succ)) ∘ Fin.castSucc) := by
          rw [hprefix']
          apply Set.iUnion_congr
          intro i
          congr 2
        rw [Set.iUnion_fin_add_one_eq_iUnion_castSucc]
        rw [← hprefix'']
        exact (Set.Icc_union_Icc_eq_Icc
          (hx.monotone (Fin.zero_le _))
          (hx (Fin.last n).castSucc_lt_succ).le).symm

private theorem exists_affineValue_eqOn_of_finite_selector {I : Set ℝ}
    (hI : IsPreconnected I) (L : Finset (ℝ × ℝ)) {f : ℝ → ℝ}
    (hf : ContinuousOn f I)
    (hsel : ∀ x ∈ I, ∃ c ∈ L, f x = affineValue c x)
    (hsep : ∀ c ∈ L, ∀ d ∈ L, c ≠ d →
      ∀ x ∈ I, affineValue c x ≠ affineValue d x)
    (hIne : I.Nonempty) :
    ∃ c ∈ L, Set.EqOn f (affineValue c) I := by
  classical
  let _ : PreconnectedSpace I := Subtype.preconnectedSpace hI
  obtain ⟨x₀, hx₀⟩ := hIne
  obtain ⟨c₀, hc₀L, hc₀⟩ := hsel x₀ hx₀
  let A : Set I := {x | f x = affineValue c₀ x}
  have hAclosed : IsClosed A := by
    apply isClosed_eq
    · change Continuous (I.domRestrict f)
      exact continuousOn_iff_continuous_domRestrict.mp hf
    · exact (continuous_affineValue c₀).comp continuous_subtype_val
  have hAc : Aᶜ = ⋃ d ∈ L.erase c₀,
      {x : I | f x = affineValue d x} := by
    ext x
    constructor
    · intro hx
      have hxne : f x ≠ affineValue c₀ x := by simpa [A] using hx
      obtain ⟨d, hdL, hd⟩ := hsel x x.2
      have hdc : d ≠ c₀ := by
        intro h
        subst d
        exact hxne hd
      exact Set.mem_iUnion₂.mpr ⟨d, Finset.mem_erase.mpr ⟨hdc, hdL⟩, hd⟩
    · intro hx
      obtain ⟨d, hdL, hd⟩ := Set.mem_iUnion₂.mp hx
      have hdc := (Finset.mem_erase.mp hdL).1
      intro hxc
      exact hsep d (Finset.mem_of_mem_erase hdL) c₀ hc₀L hdc x x.2 (hd.symm.trans hxc)
  have hAcclosed : IsClosed Aᶜ := by
    rw [hAc]
    apply isClosed_biUnion_finset
    intro d hd
    apply isClosed_eq
    · change Continuous (I.domRestrict f)
      exact continuousOn_iff_continuous_domRestrict.mp hf
    · exact (continuous_affineValue d).comp continuous_subtype_val
  have hAclopen : IsClopen A := ⟨hAclosed, isClosed_compl_iff.mp hAcclosed⟩
  have hAnonempty : A.Nonempty := ⟨⟨x₀, hx₀⟩, hc₀⟩
  have hAuniv : A = Set.univ := hAclopen.eq_univ hAnonempty
  refine ⟨c₀, hc₀L, ?_⟩
  intro x hx
  have : (⟨x, hx⟩ : I) ∈ A := hAuniv.symm ▸ Set.mem_univ _
  exact this

private theorem exists_affineValue_eqOn_Icc_of_avoids_crossings {a b : ℝ}
    (hab : a < b) (L : Finset (ℝ × ℝ)) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b))
    (hsel : ∀ x ∈ Set.Icc a b, ∃ c ∈ L, f x = affineValue c x)
    (hcross : Set.Ioo a b ∩ affineCrossings L = ∅) :
    ∃ c ∈ L, Set.EqOn f (affineValue c) (Set.Icc a b) := by
  classical
  have hf' : ContinuousOn f (Set.Ioo a b) :=
    hf.mono (Set.Ioo_subset_Icc_self)
  have hsel' : ∀ x ∈ Set.Ioo a b, ∃ c ∈ L, f x = affineValue c x :=
    fun x hx ↦ hsel x (Set.Ioo_subset_Icc_self hx)
  have hsep : ∀ c ∈ L, ∀ d ∈ L, c ≠ d →
      ∀ x ∈ Set.Ioo a b, affineValue c x ≠ affineValue d x := by
    intro c hc d hd hcd x hx hEq
    have hxCross : x ∈ affineCrossings L := by
      exact Set.mem_iUnion₂.mpr ⟨c, hc, Set.mem_iUnion₂.mpr
        ⟨d, Finset.mem_erase.mpr ⟨hcd.symm, hd⟩, hEq⟩⟩
    have : x ∈ Set.Ioo a b ∩ affineCrossings L := ⟨hx, hxCross⟩
    simp [hcross] at this
  obtain ⟨c, hcL, hc⟩ := exists_affineValue_eqOn_of_finite_selector
    isPreconnected_Ioo L hf' hsel' hsep (Set.nonempty_Ioo.mpr hab)
  refine ⟨c, hcL, ?_⟩
  exact hc.of_subset_closure hf (continuous_affineValue c).continuousOn
    Set.Ioo_subset_Icc_self (by simp [closure_Ioo hab.ne])

/-- A continuous finite selector of affine functions on a compact interval is a polyline. -/
theorem exists_graphPolyline_of_finite_affine_selector {a b : ℝ}
    (hab : a < b) (L : Finset (ℝ × ℝ)) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b))
    (hsel : ∀ x ∈ Set.Icc a b, ∃ c ∈ L, f x = affineValue c x) :
    ∃ p : XMonotonePolylineData,
      0 < p.edges ∧
      p.vertices 0 = pointOnGraph f a ∧
      p.vertices (Fin.last p.edges) = pointOnGraph f b ∧
      p.carrier = pointOnGraph f '' Set.Icc a b ∧
      (∀ i : Fin (p.edges + 1),
        p.vertices i = pointOnGraph f (p.vertices i 0)) ∧
      ∀ i : Fin p.edges, ∃ c ∈ L,
        Set.EqOn f (affineValue c)
          (Set.Icc (p.vertices i.castSucc 0) (p.vertices i.succ 0)) := by
  classical
  let C := (finite_affineCrossings L).toFinset.filter (· ∈ Set.Icc a b)
  let B := insert a (insert b C)
  have haB : a ∈ B := by simp [B]
  have hbB : b ∈ B := by simp [B]
  have hBsub : ∀ z ∈ B, z ∈ Set.Icc a b := by
    intro z hz
    simp only [B, Finset.mem_insert] at hz
    rcases hz with rfl | rfl | hz
    · exact ⟨le_rfl, hab.le⟩
    · exact ⟨hab.le, le_rfl⟩
    · exact (Finset.mem_filter.mp hz).2
  have hcard2 : 2 ≤ B.card := by
    have hsub : ({a, b} : Finset ℝ) ⊆ B := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact haB
      · exact hbB
    have hcard := Finset.card_le_card hsub
    simpa [hab.ne] using hcard
  let n := B.card - 1
  have hnpos : 0 < n := by dsimp [n]; omega
  have hcard : B.card = n + 1 := by dsimp [n]; omega
  let x : Fin (n + 1) → ℝ := B.orderEmbOfFin hcard
  have hx : StrictMono x := (B.orderEmbOfFin hcard).strictMono
  have hxmem (i : Fin (n + 1)) : x i ∈ B := by
    exact B.orderEmbOfFin_mem hcard i
  have hxrange : Set.range x = B := by
    exact B.range_orderEmbOfFin hcard
  have hxzero : x 0 = a := by
    apply le_antisymm
    · have haRange : a ∈ Set.range x := by simpa [hxrange] using haB
      obtain ⟨i, hi⟩ := haRange
      rw [← hi]
      exact hx.monotone (Fin.zero_le i)
    · exact (hBsub _ (hxmem 0)).1
  have hxlast : x (Fin.last n) = b := by
    apply le_antisymm
    · exact (hBsub _ (hxmem (Fin.last n))).2
    · have hbRange : b ∈ Set.range x := by simpa [hxrange] using hbB
      obtain ⟨i, hi⟩ := hbRange
      rw [← hi]
      exact hx.monotone (Fin.le_last i)
  have hnocross (i : Fin n) :
      Set.Ioo (x i.castSucc) (x i.succ) ∩ affineCrossings L = ∅ := by
    ext z
    constructor
    · intro hz
      have hzab : z ∈ Set.Icc a b := by
        rw [← hxzero, ← hxlast]
        exact ⟨(hx.monotone (Fin.zero_le i.castSucc)).trans hz.1.1.le,
          hz.1.2.le.trans (hx.monotone (Fin.le_last i.succ))⟩
      have hzB : z ∈ B := by
        apply Finset.mem_insert.mpr
        right
        apply Finset.mem_insert.mpr
        right
        apply Finset.mem_filter.mpr
        exact ⟨(finite_affineCrossings L).mem_toFinset.mpr hz.2, hzab⟩
      have hzRange : z ∈ Set.range x := by simpa [hxrange] using hzB
      obtain ⟨j, hj⟩ := hzRange
      rw [← hj] at hz
      have hij : i.castSucc < j := hx.lt_iff_lt.mp hz.1.1
      have hji : j < i.succ := hx.lt_iff_lt.mp hz.1.2
      change i.val < j.val at hij
      change j.val < i.val + 1 at hji
      omega
    · intro hz
      exact hz.elim
  have hpiece : ∀ i : Fin n, ∃ c ∈ L,
      Set.EqOn f (affineValue c) (Set.Icc (x i.castSucc) (x i.succ)) := by
    intro i
    exact exists_affineValue_eqOn_Icc_of_avoids_crossings
      (hx i.castSucc_lt_succ) L
      (hf.mono (Set.Icc_subset_Icc
        (by rw [← hxzero]; exact hx.monotone (Fin.zero_le _))
        (by rw [← hxlast]; exact hx.monotone (Fin.le_last _))))
      (fun z hz ↦ hsel z (Set.Icc_subset_Icc
        (by rw [← hxzero]; exact hx.monotone (Fin.zero_le _))
        (by rw [← hxlast]; exact hx.monotone (Fin.le_last _)) hz))
      (hnocross i)
  let p := graphPolyline n x hx f
  refine ⟨p, hnpos, ?_, ?_, ?_, ?_, ?_⟩
  · change pointOnGraph f (x 0) = pointOnGraph f a
    rw [hxzero]
  · change pointOnGraph f (x (Fin.last n)) = pointOnGraph f b
    rw [hxlast]
  · rw [graphPolyline_carrier_eq_image_Icc hx]
    · simp [hxzero, hxlast]
    · intro i
      obtain ⟨c, -, hc⟩ := hpiece i
      exact ⟨c.1, c.2, hc⟩
    · exact iUnion_Icc_fin hnpos hx
  · intro i
    rfl
  · intro i
    change ∃ c ∈ L, Set.EqOn f (affineValue c)
      (Set.Icc (x i.castSucc) (x i.succ))
    exact hpiece i


/-- Injective graph parametrizations preserve disjointness of parameter sets. -/
theorem pointOnGraph_image_disjoint
    (f : ℝ → ℝ) {s t : Set ℝ} (hst : Disjoint s t) :
    Disjoint (pointOnGraph f '' s) (pointOnGraph f '' t) := by
  rw [Set.disjoint_left]
  rintro q ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
  have heq : x = y := by
    have := congrArg (fun p : Point ↦ p 0) hxy
    simpa [pointOnGraph] using this.symm
  exact Set.disjoint_left.mp hst hx (heq ▸ hy)


end MovingSofa
