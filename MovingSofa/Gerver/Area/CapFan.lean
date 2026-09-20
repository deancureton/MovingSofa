import MovingSofa.Convex.ContactFanArea
import MovingSofa.Gerver.Area.Evaluator
import MovingSofa.Gerver.OuterContacts

/-!
# The support-contact fan of the Gerver outer cap

The literal Gerver outer cap is a compact convex subset of the plane lying in the closed
quadrant above the fan anchor `L = C (π / 2)`, which sits on the wall.  The `640` listed
contacts `A (t)` and `C (t)` at the grid angles attain the cap support at the strictly
increasing normals `t` and `t + π / 2` of `[0, π)`, so `supportContact_fan_area` bounds the
cap area below by half the shoelace sum of the fan over the anchor.  The certificate
encloses that sum (`capDoubledZ_sound`), and its kernel-checked numeric conclusion
`GerverAreaCert.capOK_true` turns the enclosure into `28609 / 10000 ≤ |K₀|`.
-/

noncomputable section

namespace MovingSofa

open MeasureTheory
open GerverAreaCert

/-! ### Elementary geometry of the outer cap -/

/-- The paper path starts at the origin. -/
theorem paperGerverPath_zero : paperGerverPath 0 = 0 := by
  have hreg := gerver_direct_path_regularity GerverSofa.PartB.params
    GerverSofa.PartB.params_mem GerverSofa.PartB.params_equations
  show GerverSofa.PartF.Coordinates.toPlane
    (GerverSofa.Romik.path GerverSofa.PartB.params 0) = 0
  rw [hreg.2.1]
  ext i
  fin_cases i <;> rfl

/-- The outer cap written as an intersection of closed half-planes. -/
theorem gerverOuterCap_eq_iInter :
    gerverOuterCap =
      {q : Point | 0 ≤ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))} ∩
        ⋂ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
          ({q : Point | inner ℝ q (normalVector (t : Real.Angle)) ≤
              inner ℝ (paperGerverPath t) (normalVector (t : Real.Angle)) + 1} ∩
            {q : Point | inner ℝ q (tangentVector (t : Real.Angle)) ≤
              inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) + 1}) := by
  ext q
  simp only [gerverOuterCap, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter₂,
    inner_normalVector_pi_div_two]

/-- The outer cap is closed, being an intersection of closed half-spaces. -/
theorem isClosed_gerverOuterCap : IsClosed gerverOuterCap := by
  rw [gerverOuterCap_eq_iInter]
  refine IsClosed.inter (isClosed_le continuous_const
    (continuous_id.inner continuous_const)) ?_
  exact isClosed_biInter fun t _ ↦ IsClosed.inter
    (isClosed_le (continuous_id.inner continuous_const) continuous_const)
    (isClosed_le (continuous_id.inner continuous_const) continuous_const)

/-- The outer cap is convex, being an intersection of half-spaces. -/
theorem convex_gerverOuterCap : Convex ℝ gerverOuterCap := by
  rw [gerverOuterCap_eq_iInter]
  refine Convex.inter (convex_halfSpace_ge (isLinearMap_inner_left _) 0) ?_
  exact convex_iInter₂ fun t _ ↦ Convex.inter
    (convex_halfSpace_le (isLinearMap_inner_left _) _)
    (convex_halfSpace_le (isLinearMap_inner_left _) _)

/-- The outer cap is contained in an explicit coordinate rectangle. -/
theorem gerverOuterCap_subset_box :
    gerverOuterCap ⊆ {p : Point |
      p 0 ∈ Set.Icc (-(inner ℝ (paperGerverPath (Real.pi / 2))
        (tangentVector ((Real.pi / 2 : ℝ) : Real.Angle)) + 1)) 1 ∧ p 1 ∈ Set.Icc 0 1} := by
  have hTpos : (0 : ℝ) < Real.pi / 2 := by positivity
  intro q hq
  obtain ⟨hy, hcap⟩ := hq
  have h0 := hcap 0 ⟨le_rfl, hTpos.le⟩
  have hT := hcap (Real.pi / 2) ⟨hTpos.le, le_rfl⟩
  rw [paperGerverPath_zero, inner_normalVector_zero, inner_normalVector_zero,
    inner_tangentVector_zero, inner_tangentVector_zero] at h0
  refine ⟨⟨?_, ?_⟩, hy, ?_⟩
  · have h := hT.2
    rw [inner_tangentVector_pi_div_two] at h
    linarith
  · have h := h0.1
    simpa using h
  · have h := h0.2
    simpa using h

/-- The outer cap is compact: it is closed and contained in a coordinate rectangle. -/
theorem isCompact_gerverOuterCap : IsCompact gerverOuterCap := by
  refine Metric.isCompact_of_isClosed_isBounded isClosed_gerverOuterCap ?_
  set c : ℝ := -(inner ℝ (paperGerverPath (Real.pi / 2))
    (tangentVector ((Real.pi / 2 : ℝ) : Real.Angle)) + 1) with hc
  set K : ℝ := |c| + 1 with hK
  rw [isBounded_iff_forall_norm_le]
  refine ⟨2 * K, fun q hq ↦ ?_⟩
  obtain ⟨⟨hx0, hx1⟩, hy0, hy1⟩ := gerverOuterCap_subset_box hq
  have hK1 : (1 : ℝ) ≤ K := by rw [hK]; linarith [abs_nonneg c]
  have hsq : ‖q‖ ^ 2 = q 0 ^ 2 + q 1 ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    simp [Fin.sum_univ_two, sq_abs]
  have hx : |q 0| ≤ K := by
    rw [abs_le]
    refine ⟨?_, by rw [hK]; linarith [abs_nonneg c]⟩
    have hcle : -|c| ≤ c := neg_abs_le c
    rw [hK]
    linarith [hx0]
  have hy : |q 1| ≤ K := by
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have hx2 : q 0 ^ 2 ≤ K ^ 2 := by nlinarith [sq_abs (q 0), abs_nonneg (q 0)]
  have hy2 : q 1 ^ 2 ≤ K ^ 2 := by nlinarith [sq_abs (q 1), abs_nonneg (q 1)]
  nlinarith [norm_nonneg q, hsq, hx2, hy2, hK1]

/-- The outer cap is Borel measurable. -/
theorem measurableSet_gerverOuterCap : MeasurableSet gerverOuterCap :=
  isClosed_gerverOuterCap.measurableSet

/-- The outer cap has finite planar volume. -/
theorem volume_gerverOuterCap_lt_top : volume gerverOuterCap < ⊤ :=
  isCompact_gerverOuterCap.measure_lt_top

/-! ### The support-contact fan and the cap lower bound -/

/-- The fan anchor `L = C (π / 2)`. -/
def gerverFanAnchor : Point := paperGerverContacts (Real.pi / 2) 2

/-- The `i`-th listed support contact, `i < fanCount`. -/
def gerverFanPoint (i : ℕ) : Point :=
  gerverContactPoint (fanKind i) (gerverGridTime (fanIdx i))

/-- The support normal of the `i`-th listed contact. -/
def gerverFanNormal (i : ℕ) : ℝ :=
  if i ≤ 5 * NN then gerverGridTime i else gerverGridTime (i - 5 * NN) + Real.pi / 2

/-- The support value of the first outer contact in its own normal direction. -/
private theorem inner_paperGerverContacts_zero_normalVector (t : ℝ) :
    inner ℝ (paperGerverContacts t 0) (normalVector (t : Real.Angle)) =
      inner ℝ (paperGerverPath t) (normalVector (t : Real.Angle)) + 1 := by
  show inner ℝ (paperGerverPath t +
    (paperGerverVelocityComponents t).1 • tangentVector (t : Real.Angle) +
      normalVector (t : Real.Angle)) (normalVector (t : Real.Angle)) = _
  rw [inner_add_left, inner_add_left, real_inner_smul_left,
    inner_tangentVector_normalVector_real, inner_normalVector_self]
  simp

/-- The support value of the third outer contact in the rotated normal direction. -/
private theorem inner_paperGerverContacts_two_tangentVector (t : ℝ) :
    inner ℝ (paperGerverContacts t 2) (tangentVector (t : Real.Angle)) =
      inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) + 1 := by
  show inner ℝ (paperGerverPath t -
    (paperGerverVelocityComponents t).2 • normalVector (t : Real.Angle) +
      tangentVector (t : Real.Angle)) (tangentVector (t : Real.Angle)) = _
  rw [inner_add_left, inner_sub_left, real_inner_smul_left,
    inner_normalVector_tangentVector, inner_tangentVector_self]
  ring

/-- `A t` attains the cap support at normal `t`. -/
theorem gerverOuterCap_support_A (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2))
    {q : Point} (hq : q ∈ gerverOuterCap) :
    inner ℝ q (normalVector (t : Real.Angle)) ≤
      inner ℝ (paperGerverContacts t 0) (normalVector (t : Real.Angle)) := by
  rw [inner_paperGerverContacts_zero_normalVector]
  exact (hq.2 t ht).1

/-- `C t` attains the cap support at normal `t + π / 2`. -/
theorem gerverOuterCap_support_C (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2))
    {q : Point} (hq : q ∈ gerverOuterCap) :
    inner ℝ q (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) ≤
      inner ℝ (paperGerverContacts t 2) (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) := by
  rw [normalVector_add_pi_div_two_real, inner_paperGerverContacts_two_tangentVector]
  exact (hq.2 t ht).2

/-- The anchor sits on the wall. -/
theorem gerverFanAnchor_snd : gerverFanAnchor 1 = 0 := by
  have hTpos : (0 : ℝ) < Real.pi / 2 := by positivity
  have hT : (Real.pi / 2) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨hTpos.le, le_rfl⟩
  have h := congrArg Prod.snd (fromPlane_paperGerverContacts (Real.pi / 2) hT 2)
  have hC : (GerverSofa.PartC.C (Real.pi / 2)).2 = 0 :=
    GerverSofa.PartC.Stage2.C_T_snd_zero
  show (GerverSofa.PartF.Coordinates.fromPlane (paperGerverContacts (Real.pi / 2) 2)).2 = 0
  rw [h]
  simpa using hC

/-- The cap lies in the closed quadrant above the anchor. -/
theorem gerverOuterCap_quadrant {q : Point} (hq : q ∈ gerverOuterCap) :
    gerverFanAnchor 0 ≤ q 0 ∧ 0 ≤ q 1 := by
  have hTpos : (0 : ℝ) < Real.pi / 2 := by positivity
  have hT : (Real.pi / 2) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨hTpos.le, le_rfl⟩
  refine ⟨?_, hq.1⟩
  have h := gerverOuterCap_support_C (Real.pi / 2) hT hq
  have hsplit : (Real.pi / 2 + Real.pi / 2 : ℝ) = 0 + Real.pi := by ring
  rw [hsplit, normalVector_add_pi, inner_neg_right, inner_neg_right,
    inner_normalVector_zero, inner_normalVector_zero] at h
  show gerverFanAnchor 0 ≤ q 0
  simp only [gerverFanAnchor]
  linarith

/-- The listed support normals are strictly increasing. -/
theorem gerverFanNormal_lt_succ (i : ℕ) (hi : i + 1 < fanCount) :
    gerverFanNormal i < gerverFanNormal (i + 1) := by
  have hNN : NN = 64 := rfl
  simp only [fanCount] at hi
  simp only [gerverFanNormal]
  split_ifs with h1 h2
  · exact gerverGridTime_lt_succ i (by omega)
  · have hi5 : i = 5 * NN := by omega
    subst hi5
    rw [Nat.add_sub_cancel_left, gerverGridTime_top]
    have h0 : gerverGridTime 0 < gerverGridTime 1 := gerverGridTime_lt_succ 0 (by omega)
    rw [gerverGridTime_zero] at h0
    linarith
  · omega
  · have hrw : i + 1 - 5 * NN = (i - 5 * NN) + 1 := by omega
    rw [hrw]
    have h := gerverGridTime_lt_succ (i - 5 * NN) (by omega)
    linarith

/-- The listed support normals lie in `[0, π)`. -/
theorem gerverFanNormal_mem_Ico (i : ℕ) (hi : i < fanCount) :
    0 ≤ gerverFanNormal i ∧ gerverFanNormal i < Real.pi := by
  have hNN : NN = 64 := rfl
  simp only [fanCount] at hi
  have hTpos : (0 : ℝ) < Real.pi / 2 := by positivity
  simp only [gerverFanNormal]
  split_ifs with h1
  · obtain ⟨hlo, hhi⟩ := gerverGridTime_mem_Icc i h1
    exact ⟨hlo, by linarith⟩
  · have hlt : i - 5 * NN < 5 * NN := by omega
    have hstrict := gerverGridTime_lt_of_lt hlt le_rfl
    rw [gerverGridTime_top] at hstrict
    obtain ⟨hlo, -⟩ := gerverGridTime_mem_Icc (i - 5 * NN) hlt.le
    exact ⟨by linarith, by linarith⟩

/-- The `kind = 1` slot of the contact dictionary is the first outer contact. -/
private theorem gerverContactPoint_one (x : ℝ) :
    gerverContactPoint 1 x = paperGerverContacts x 0 := rfl

/-- The `kind = 3` slot of the contact dictionary is the third outer contact. -/
private theorem gerverContactPoint_three (x : ℝ) :
    gerverContactPoint 3 x = paperGerverContacts x 2 := rfl

/-- Every listed contact lies in the cap. -/
theorem gerverFanPoint_mem (i : ℕ) (hi : i < fanCount) :
    gerverFanPoint i ∈ gerverOuterCap := by
  have hNN : NN = 64 := rfl
  simp only [fanCount] at hi
  simp only [gerverFanPoint, fanKind, fanIdx]
  split_ifs with h1
  · rw [gerverContactPoint_one]
    exact gerver_outer_contact_A _ (gerverGridTime_mem_Icc i h1)
  · rw [gerverContactPoint_three]
    exact gerver_outer_contact_C _ (gerverGridTime_mem_Icc (i - 5 * NN) (by omega))

/-- Every listed contact attains the cap support at its listed normal. -/
theorem gerverFanPoint_support (i : ℕ) (hi : i < fanCount) {q : Point}
    (hq : q ∈ gerverOuterCap) :
    inner ℝ q (normalVector (gerverFanNormal i : Real.Angle)) ≤
      inner ℝ (gerverFanPoint i) (normalVector (gerverFanNormal i : Real.Angle)) := by
  have hNN : NN = 64 := rfl
  simp only [fanCount] at hi
  simp only [gerverFanPoint, gerverFanNormal, fanKind, fanIdx]
  split_ifs with h1
  · rw [gerverContactPoint_one]
    exact gerverOuterCap_support_A _ (gerverGridTime_mem_Icc i h1) hq
  · rw [gerverContactPoint_three]
    exact gerverOuterCap_support_C _ (gerverGridTime_mem_Icc (i - 5 * NN) (by omega)) hq

/-- The certificate encloses both coordinates of every listed fan contact. -/
private theorem fanZ_sound (i : ℕ) (hi : i < fanCount) :
    SI.Contains (fanZ i).1 (gerverFanPoint i 0) ∧
      SI.Contains (fanZ i).2 (gerverFanPoint i 1) := by
  have hNN : NN = 64 := rfl
  simp only [fanCount] at hi
  have hidx : fanIdx i ≤ 5 * NN := by
    simp only [fanIdx]
    split_ifs with h <;> omega
  have hkind : fanKind i ≤ 4 := by
    simp only [fanKind]
    split_ifs <;> norm_num
  exact contactZ_sound (fanIdx i) hidx (fanKind i) hkind

/-- The certificate encloses both coordinates of the fan anchor. -/
private theorem anchorZ_sound :
    SI.Contains anchorZ.1 (gerverFanAnchor 0) ∧ SI.Contains anchorZ.2 (gerverFanAnchor 1) := by
  have h := contactZ_sound (5 * NN) le_rfl 3 (by norm_num)
  rwa [gerverGridTime_top] at h

/-- The certificate encloses the fan shoelace sum. -/
theorem capDoubledZ_sound :
    SI.Contains capDoubledZ (∑ i ∈ Finset.range (fanCount - 1),
      planeCrossProduct (gerverFanPoint i - gerverFanAnchor)
        (gerverFanPoint (i + 1) - gerverFanAnchor)) := by
  have hNN : NN = 64 := rfl
  refine SI.contains_foldl_range (fanCount - 1) fun i hi => ?_
  simp only [fanCount] at hi
  obtain ⟨ha1, ha2⟩ := fanZ_sound i (by simp only [fanCount]; omega)
  obtain ⟨hb1, hb2⟩ := fanZ_sound (i + 1) (by simp only [fanCount]; omega)
  obtain ⟨hL1, hL2⟩ := anchorZ_sound
  have hcross : planeCrossProduct (gerverFanPoint i - gerverFanAnchor)
      (gerverFanPoint (i + 1) - gerverFanAnchor) =
      (gerverFanPoint i 0 - gerverFanAnchor 0) *
          (gerverFanPoint (i + 1) 1 - gerverFanAnchor 1) -
        (gerverFanPoint i 1 - gerverFanAnchor 1) *
          (gerverFanPoint (i + 1) 0 - gerverFanAnchor 0) := by
    simp [planeCrossProduct]
  rw [hcross]
  exact SI.contains_sub
    (SI.contains_mul (SI.contains_sub ha1 hL1) (SI.contains_sub hb2 hL2))
    (SI.contains_mul (SI.contains_sub ha2 hL2) (SI.contains_sub hb1 hL1))

/-- The cap area lower bound. -/
theorem gerverOuterCap_area_certified_lower_bound :
    (28609 : ℝ) / 10000 ≤ ClassicalResults.area gerverOuterCap := by
  have hNN : NN = 64 := rfl
  have hTpos : (0 : ℝ) < Real.pi / 2 := by positivity
  have hcount : fanCount = 640 := rfl
  -- The fan data on `Fin 640`.
  have hlt : ∀ i : Fin 640, (i : ℕ) < fanCount := fun i => by
    rw [hcount]; exact i.isLt
  have hmono : StrictMono fun i : Fin 640 => gerverFanNormal (i : ℕ) := by
    refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
    simpa using gerverFanNormal_lt_succ (i : ℕ) (by rw [hcount]; omega)
  obtain ⟨-, hfan⟩ := supportContact_fan_area gerverOuterCap
    ⟨gerverFanPoint 0, gerverFanPoint_mem 0 (by rw [hcount]; norm_num)⟩
    isCompact_gerverOuterCap convex_gerverOuterCap gerverFanAnchor
    (gerver_outer_contact_C (Real.pi / 2) ⟨hTpos.le, le_rfl⟩)
    gerverFanAnchor_snd (fun _ hq => gerverOuterCap_quadrant hq) 639 (by norm_num)
    (fun i : Fin 640 => gerverFanNormal (i : ℕ)) hmono
    (fun i => gerverFanNormal_mem_Ico (i : ℕ) (hlt i))
    (fun i : Fin 640 => gerverFanPoint (i : ℕ)) (fun i => gerverFanPoint_mem (i : ℕ) (hlt i))
    (fun i q hq => gerverFanPoint_support (i : ℕ) (hlt i) hq)
  -- Identify the `Fin`-indexed fan sum with the certificate's range sum.
  rw [show (∑ i : Fin 639, planeCrossProduct
        (gerverFanPoint (i.castSucc : Fin 640) - gerverFanAnchor)
        (gerverFanPoint (i.succ : Fin 640) - gerverFanAnchor)) =
      ∑ i ∈ Finset.range (fanCount - 1),
        planeCrossProduct (gerverFanPoint i - gerverFanAnchor)
          (gerverFanPoint (i + 1) - gerverFanAnchor) by
    rw [hcount]
    exact Fin.sum_univ_eq_sum_range (fun i => planeCrossProduct
      (gerverFanPoint i - gerverFanAnchor) (gerverFanPoint (i + 1) - gerverFanAnchor)) 639] at hfan
  -- The kernel-checked numeric inequality.  The fan sum and the certificate endpoint are
  -- abstracted into local variables first, and the arithmetic tactics are used in their
  -- `only` form, so that no tactic ever tries to evaluate the 639-term fold.
  obtain ⟨S, hS⟩ : ∃ S : ℝ, (∑ i ∈ Finset.range (fanCount - 1),
      planeCrossProduct (gerverFanPoint i - gerverFanAnchor)
        (gerverFanPoint (i + 1) - gerverFanAnchor)) = S := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : ℤ, capDoubledZ.lo = z := ⟨_, rfl⟩
  obtain ⟨hlo, -⟩ := capDoubledZ_sound
  rw [hS] at hfan
  rw [hS, hz] at hlo
  have hOK : 2 * 28609 * M ≤ 10000 * capDoubledZ.lo := by
    have h := capOK_true
    unfold capOK at h
    exact of_decide_eq_true h
  rw [hz] at hOK
  have hOK' : (2 * 28609 * (M : ℝ)) ≤ 10000 * (z : ℝ) := by exact_mod_cast hOK
  have hM : (0 : ℝ) < (M : ℝ) := SI.Mpos
  have hkey : 2 * 28609 ≤ 10000 * S := by nlinarith only [hlo, hOK', hM]
  refine le_trans ?_ hfan
  linarith only [hkey]

end MovingSofa
