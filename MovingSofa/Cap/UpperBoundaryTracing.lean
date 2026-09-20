import MovingSofa.Cap.Special.Domain
import MovingSofa.Area.ModuloLinear
import MovingSofa.Convex.ArcArea
import MovingSofa.Cap.LowerNormalMeasure

/-!
# Tracing the area of a special cap along its upper boundary

The area of a convex body is half the integral of its support function against its surface area
measure.  For a special cap that measure is carried by the closed upper semicircle of normals,
because the two open quarter arcs of lower normals carry degenerate faces
(`MovingSofa.CapSpace.surfaceAreaMeasure_image_Ioo_lower_eq_zero`) and the bottom normal carries
support value zero.  The injectivity condition provides angular densities on the two upper quarter
circles, so the four distinguished angles `0`, `φᴿ`, `φᴸ` and `π` are not atoms, and the semicircle
splits — up to a null set — into the four open arcs `(0, φᴿ)`, `(φᴿ, φᴸ)`, `(φᴸ, π / 2)`,
`(π / 2, π)` and the top normal `π / 2`.  Each open arc is shorter than `π`, so the convex arc area
formula applies to it, and the top normal contributes half the mass of a single atom
(`MovingSofa.HasCapDensities.area_eq_upper_arcs_add_top_atom`).  Evaluating the surface area
measure at that fixed angle is convex-linear on the convex domain of special caps, whence the cap
area agrees with the sum of the four arc areas modulo convex-linear functionals
(`MovingSofa.specialCapArea_equivalent_upper_arcs`).
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace MovingSofa

/-- On an open arc shorter than `π` the support-area integral is twice the convex arc area. -/
private theorem setIntegral_image_Ioo_eq_two_mul_convexArcArea (K : ConvexBody Point)
    {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi) :
    ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
        supportValue (K : Set Point) t ∂surfaceAreaMeasure K =
      2 * convexArcArea K a b := by
  rw [(convexArc_area a b hab hba).2.1 K]
  ring

/-- Up to half the mass of the atom at its top normal, the area of a right-angle cap carrying
angular densities is the sum of the areas of the four upper boundary arcs cut out by the two
distinguished Gerver angles. -/
theorem HasCapDensities.area_eq_upper_arcs_add_top_atom {C : RightAngleCapSpace}
    {dr dl : ℝ → ℝ≥0} (hdens : HasCapDensities C dr dl) :
    ClassicalResults.area (C.val : Set Point) =
      (convexArcArea C.val 0 paperGerverConstants.2.1 +
          convexArcArea C.val paperGerverConstants.2.1 paperGerverConstants.2.2 +
          convexArcArea C.val paperGerverConstants.2.2 (Real.pi / 2) +
          convexArcArea C.val (Real.pi / 2) Real.pi) +
        (surfaceAreaMeasure C.val {((Real.pi / 2 : ℝ) : Real.Angle)}).toReal / 2 := by
  have hpi := Real.pi_pos
  obtain ⟨⟨hrpos, -⟩, ⟨-, hlT⟩, -⟩ := paperGerverConstants_snd_mem_Ioo
  have hrl := paperGerverConstants_snd_fst_lt_snd_snd
  set r := paperGerverConstants.2.1
  set l := paperGerverConstants.2.2
  -- ### The surface measure is finite, so the continuous support function is integrable
  have hfinite : IsFiniteMeasure (surfaceAreaMeasure C.val) :=
    (surfaceAreaMeasure_face_union C.val).1
  have hint : Integrable (fun a : Real.Angle ↦ supportValue (C.val : Set Point) a)
      (surfaceAreaMeasure C.val) :=
    ((compactSet_support_continuity (C.val : Set Point) (C.val : Set Point) C.val.nonempty'
      C.val.isCompact' C.val.nonempty' C.val.isCompact').2.2.1).integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _))
  -- ### The five pieces of the closed upper semicircle that carry the surface measure
  set U : Set ℝ := Set.Ioo 0 r ∪ Set.Ioo r l ∪ Set.Ioo l (Real.pi / 2) ∪
    Set.Ioo (Real.pi / 2) Real.pi ∪ {Real.pi / 2} with hUdef
  have hs1 : Set.Ioo (0 : ℝ) r ⊆ Set.Ioc 0 (2 * Real.pi) := fun x hx ↦
    ⟨hx.1, by linarith [hx.2]⟩
  have hs2 : Set.Ioo r l ⊆ Set.Ioc 0 (2 * Real.pi) := fun x hx ↦
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hs3 : Set.Ioo l (Real.pi / 2) ⊆ Set.Ioc 0 (2 * Real.pi) := fun x hx ↦
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hs4 : Set.Ioo (Real.pi / 2) Real.pi ⊆ Set.Ioc 0 (2 * Real.pi) := fun x hx ↦
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hs5 : ({Real.pi / 2} : Set ℝ) ⊆ Set.Ioc 0 (2 * Real.pi) := by
    rintro x rfl
    exact ⟨by linarith, by linarith⟩
  have hUsub : U ⊆ Set.Ioc 0 (2 * Real.pi) :=
    Set.union_subset (Set.union_subset (Set.union_subset (Set.union_subset hs1 hs2) hs3) hs4) hs5
  have hUIcc : U ⊆ Set.Icc 0 Real.pi := by
    refine Set.union_subset (Set.union_subset (Set.union_subset (Set.union_subset
      (fun x hx ↦ ⟨hx.1.le, by linarith [hx.2]⟩)
      (fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩))
      (fun x hx ↦ ⟨by linarith [hx.1], by linarith [hx.2]⟩))
      (fun x hx ↦ ⟨by linarith [hx.1], hx.2.le⟩)) ?_
    rintro x rfl
    exact ⟨by linarith, by linarith⟩
  have hUmeas : MeasurableSet U :=
    (((measurableSet_Ioo.union measurableSet_Ioo).union measurableSet_Ioo).union
      measurableSet_Ioo).union (measurableSet_singleton _)
  -- ### Angular images of disjoint pieces of one turn are disjoint, and Borel pieces stay Borel
  have hdisj : ∀ {X Y : Set ℝ}, X ⊆ Set.Ioc 0 (2 * Real.pi) →
      Y ⊆ Set.Ioc 0 (2 * Real.pi) → Disjoint X Y →
      Disjoint ((fun t : ℝ ↦ (t : Real.Angle)) '' X)
        ((fun t : ℝ ↦ (t : Real.Angle)) '' Y) := by
    intro X Y hX hY hXY
    rw [Set.disjoint_left]
    rintro a ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
    have hyx' : y = x :=
      Real.Angle.injOn_coe_Ioc (a := 0) (b := 2 * Real.pi) (by linarith) (hY hy) (hX hx) hyx
    exact Set.disjoint_left.mp hXY hx (hyx' ▸ hy)
  have hmimg : ∀ {Y : Set ℝ}, MeasurableSet Y → Y ⊆ Set.Ioc 0 (2 * Real.pi) →
      MeasurableSet ((fun t : ℝ ↦ (t : Real.Angle)) '' Y) := fun hY hYs ↦
    Real.Angle.measurableSet_image_of_subset_Ioc (by linarith) hY hYs
  -- ### Splitting the last piece off an angular union
  have hstep : ∀ {X Y : Set ℝ}, X ⊆ Set.Ioc 0 (2 * Real.pi) →
      Y ⊆ Set.Ioc 0 (2 * Real.pi) → Disjoint X Y → MeasurableSet Y →
      ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' (X ∪ Y),
          supportValue (C.val : Set Point) t ∂surfaceAreaMeasure C.val =
        (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' X,
            supportValue (C.val : Set Point) t ∂surfaceAreaMeasure C.val) +
          ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Y,
            supportValue (C.val : Set Point) t ∂surfaceAreaMeasure C.val := by
    intro X Y hX hY hXY hmY
    rw [Set.image_union, setIntegral_union (hdisj hX hY hXY) (hmimg hmY hY)
      hint.integrableOn hint.integrableOn]
  -- ### The four distinguished angles of the upper semicircle are not atoms
  have hatom0 : surfaceAreaMeasure C.val {((0 : ℝ) : Real.Angle)} = 0 :=
    hdens.surfaceAreaMeasure_singleton_eq_zero_of_mem_Ico ⟨le_rfl, by positivity⟩
  have hatomr : surfaceAreaMeasure C.val {(r : Real.Angle)} = 0 :=
    hdens.surfaceAreaMeasure_singleton_eq_zero_of_mem_Ico ⟨hrpos.le, by linarith⟩
  have hatoml : surfaceAreaMeasure C.val {(l : Real.Angle)} = 0 :=
    hdens.surfaceAreaMeasure_singleton_eq_zero_of_mem_Ico ⟨by linarith, hlT⟩
  have hatompi : surfaceAreaMeasure C.val {((Real.pi : ℝ) : Real.Angle)} = 0 := by
    have h := hdens.surfaceAreaMeasure_singleton_eq_zero_of_mem_Ioc
      (t := Real.pi / 2) ⟨by positivity, le_rfl⟩
    rwa [show (Real.pi / 2 + Real.pi / 2 : ℝ) = Real.pi by ring] at h
  -- ### The five pieces cover the upper semicircle up to those four angles
  have hcover : Set.Icc (0 : ℝ) Real.pi ⊆ U ∪ {0, r, l, Real.pi} := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with h0 | h0
    · exact Or.inr (by simp [← h0])
    rcases lt_trichotomy x r with h | h | h
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨h0, h⟩))))
    · exact Or.inr (by simp [h])
    rcases lt_trichotomy x l with h' | h' | h'
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨h, h'⟩))))
    · exact Or.inr (by simp [h'])
    rcases lt_trichotomy x (Real.pi / 2) with h'' | h'' | h''
    · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨h', h''⟩)))
    · exact Or.inl (Or.inr h'')
    rcases eq_or_lt_of_le hx.2 with h₃ | h₃
    · exact Or.inr (by simp [h₃])
    · exact Or.inl (Or.inl (Or.inr ⟨h'', h₃⟩))
  have hnull : surfaceAreaMeasure C.val
      ((fun t : ℝ ↦ (t : Real.Angle)) '' Set.Icc 0 Real.pi \
        (fun t : ℝ ↦ (t : Real.Angle)) '' U) = 0 := by
    refine measure_mono_null (t := {((0 : ℝ) : Real.Angle), (r : Real.Angle), (l : Real.Angle),
      ((Real.pi : ℝ) : Real.Angle)}) ?_ ?_
    · rw [Set.sdiff_subset_iff]
      refine (Set.image_mono hcover).trans ?_
      rw [Set.image_union]
      exact Set.union_subset_union_right _ (by simp [Set.image_insert_eq])
    · simp only [Set.insert_eq]
      exact measure_union_null hatom0
        (measure_union_null hatomr (measure_union_null hatoml hatompi))
  -- ### The support-area integral is carried by the angular image of the five pieces
  have hSmeas : MeasurableSet ((fun t : ℝ ↦ (t : Real.Angle)) '' Set.Icc 0 Real.pi) :=
    (isCompact_Icc.image Real.Angle.continuous_coe).isClosed.measurableSet
  have htotal : ∫ a, supportValue (C.val : Set Point) a ∂surfaceAreaMeasure C.val =
      ∫ a in (fun t : ℝ ↦ (t : Real.Angle)) '' U,
        supportValue (C.val : Set Point) a ∂surfaceAreaMeasure C.val := by
    rw [← integral_add_compl hSmeas hint,
      C.setIntegral_compl_image_Icc_zero_pi_eq_zero _ C.property.2.2.2.2.2.1, add_zero,
      ← Set.union_sdiff_cancel (Set.image_mono hUIcc),
      setIntegral_union Set.disjoint_sdiff_right (hSmeas.diff (hmimg hUmeas hUsub))
        hint.integrableOn hint.integrableOn,
      setIntegral_measure_zero _ hnull, add_zero]
  -- ### The four short arcs contribute their arc areas and the top normal its atom
  have hI1 : ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo (0 : ℝ) r,
      supportValue (C.val : Set Point) t ∂surfaceAreaMeasure C.val =
      2 * convexArcArea C.val 0 r :=
    setIntegral_image_Ioo_eq_two_mul_convexArcArea C.val hrpos (by linarith)
  have hI2 : ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo r l,
      supportValue (C.val : Set Point) t ∂surfaceAreaMeasure C.val =
      2 * convexArcArea C.val r l :=
    setIntegral_image_Ioo_eq_two_mul_convexArcArea C.val hrl (by linarith)
  have hI3 : ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo l (Real.pi / 2),
      supportValue (C.val : Set Point) t ∂surfaceAreaMeasure C.val =
      2 * convexArcArea C.val l (Real.pi / 2) :=
    setIntegral_image_Ioo_eq_two_mul_convexArcArea C.val hlT (by linarith)
  have hI4 : ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo (Real.pi / 2) Real.pi,
      supportValue (C.val : Set Point) t ∂surfaceAreaMeasure C.val =
      2 * convexArcArea C.val (Real.pi / 2) Real.pi :=
    setIntegral_image_Ioo_eq_two_mul_convexArcArea C.val (by linarith) (by linarith)
  have hIT : ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' ({Real.pi / 2} : Set ℝ),
      supportValue (C.val : Set Point) t ∂surfaceAreaMeasure C.val =
      (surfaceAreaMeasure C.val {((Real.pi / 2 : ℝ) : Real.Angle)}).toReal := by
    rw [Set.image_singleton, integral_singleton, C.property.2.2.2.1, smul_eq_mul, mul_one,
      measureReal_def]
  -- ### Assembling the support-area identity
  rw [convexBody_area_support_integral.1 C.val, htotal, hUdef,
    hstep (Set.union_subset (Set.union_subset (Set.union_subset hs1 hs2) hs3) hs4) hs5
      (by rw [Set.disjoint_singleton_right]
          rintro (((⟨-, h⟩ | ⟨-, h⟩) | ⟨-, h⟩) | ⟨h, -⟩) <;> linarith)
      (measurableSet_singleton _),
    hstep (Set.union_subset (Set.union_subset hs1 hs2) hs3) hs4
      (by rw [Set.disjoint_left]
          rintro x ((⟨-, h⟩ | ⟨-, h⟩) | ⟨-, h⟩) ⟨h', -⟩ <;> linarith)
      measurableSet_Ioo,
    hstep (Set.union_subset hs1 hs2) hs3
      (by rw [Set.disjoint_left]
          rintro x (⟨-, h⟩ | ⟨-, h⟩) ⟨h', -⟩ <;> linarith)
      measurableSet_Ioo,
    hstep hs1 hs2
      (by rw [Set.disjoint_left]
          rintro x ⟨-, h⟩ ⟨h', -⟩
          linarith)
      measurableSet_Ioo,
    hI1, hI2, hI3, hI4, hIT]
  ring

theorem specialCapArea_equivalent_upper_arcs :
    EquivalentModuloConvexLinear specialCapCombination
      (fun K ↦ ClassicalResults.area (K.val.val : Set Point))
      (fun K ↦ convexArcArea K.val.val 0 paperGerverConstants.2.1 +
        convexArcArea K.val.val paperGerverConstants.2.1 paperGerverConstants.2.2 +
        convexArcArea K.val.val paperGerverConstants.2.2 (Real.pi / 2) +
        convexArcArea K.val.val (Real.pi / 2) Real.pi) := by
  -- ### The discrepancy is half the mass of the surface measure at the fixed top normal
  have key : ∀ M : SpecialCapSpace,
      ClassicalResults.area (M.val.val : Set Point) -
        (convexArcArea M.val.val 0 paperGerverConstants.2.1 +
          convexArcArea M.val.val paperGerverConstants.2.1 paperGerverConstants.2.2 +
          convexArcArea M.val.val paperGerverConstants.2.2 (Real.pi / 2) +
          convexArcArea M.val.val (Real.pi / 2) Real.pi) =
        (surfaceAreaMeasure M.val.val {((Real.pi / 2 : ℝ) : Real.Angle)}).toReal / 2 :=
    fun M ↦ by
      obtain ⟨dr, dl, hdens, -⟩ := M.property.1.1
      rw [hdens.area_eq_upper_arcs_add_top_atom]
      ring
  intro t K L
  have hKfin : IsFiniteMeasure (surfaceAreaMeasure K.val.val) :=
    (surfaceAreaMeasure_face_union K.val.val).1
  have hLfin : IsFiniteMeasure (surfaceAreaMeasure L.val.val) :=
    (surfaceAreaMeasure_face_union L.val.val).1
  simp only [realCombination, key]
  rw [specialCap_isConvexDomain.1 t K L, surfaceAreaMeasure_convexBodyCombination,
    Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
    ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)),
    ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by linarith [t.2.2] : (0 : ℝ) ≤ 1 - (t : ℝ)),
    ENNReal.toReal_ofReal t.2.1]
  ring

end MovingSofa
