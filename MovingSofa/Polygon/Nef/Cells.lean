import MovingSofa.Polygon.Nef.Basic
import MovingSofa.Geometry.Frame
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic

noncomputable section

namespace MovingSofa.Nef

open Filter Topology

lemma monotoneBoolean_update_false {n : ℕ} {E : BooleanFunction n}
    (hE : IsMonotoneBooleanFunction E) (P : Fin n → Bool) (i : Fin n) :
    E (Function.update P i false) = true → E P = true := by
  apply hE
  intro j hj
  by_cases hji : j = i
  · subst j
    simp at hj
  · simpa [Function.update_of_ne hji] using hj

lemma monotoneBoolean_update_true {n : ℕ} {E : BooleanFunction n}
    (hE : IsMonotoneBooleanFunction E) (P : Fin n → Bool) (i : Fin n) :
    E P = true → E (Function.update P i true) = true := by
  apply hE
  intro j hj
  by_cases hji : j = i
  · subst j
    simp
  · simpa [Function.update_of_ne hji] using hj

lemma monotoneBoolean_eval_iff {n : ℕ} {E : BooleanFunction n}
    (hE : IsMonotoneBooleanFunction E) (P : Fin n → Bool) (i : Fin n) :
    E P = true ↔ E (Function.update P i false) = true ∨
      (P i = true ∧ E (Function.update P i true) = true) := by
  constructor
  · intro h
    cases hp : P i
    · left
      rwa [← hp, Function.update_eq_self]
    · exact Or.inr ⟨rfl, monotoneBoolean_update_true hE P i h⟩
  · rintro (h | ⟨hp, h⟩)
    · exact monotoneBoolean_update_false hE P i h
    · rwa [(Function.update_eq_self_iff).mpr hp.symm] at h

lemma booleanSet_update_eq {n : ℕ} {E : BooleanFunction n}
    (hE : IsMonotoneBooleanFunction E) (H : Fin n → Set Point) (i : Fin n)
    (S : Set Point) :
    booleanSet E (Function.update H i S) =
      booleanSet E (Function.update H i ∅) ∪
        (S ∩ booleanSet E (Function.update H i Set.univ)) := by
  classical
  ext p
  have hfun (T : Set Point) :
      (fun j ↦ decide (p ∈ Function.update H i T j)) =
        Function.update (fun j ↦ decide (p ∈ H j)) i (decide (p ∈ T)) := by
    funext j
    by_cases hji : j = i <;> simp [hji, Function.update_of_ne]
  simp only [booleanSet, Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, hfun]
  simp only [Set.mem_empty_iff_false, decide_false, Set.mem_univ, decide_true]
  have h := monotoneBoolean_eval_iff hE
    (Function.update (fun j ↦ decide (p ∈ H j)) i (decide (p ∈ S))) i
  simpa only [Function.update_idem, Function.update_self, decide_eq_true_eq] using h

lemma booleanSet_update_sdiff {n : ℕ} {E : BooleanFunction n}
    (hE : IsMonotoneBooleanFunction E) (H : Fin n → Set Point) (i : Fin n)
    (S T : Set Point) :
    booleanSet E (Function.update H i S) \ booleanSet E (Function.update H i T) =
      (S \ T) ∩ (booleanSet E (Function.update H i Set.univ) \
        booleanSet E (Function.update H i ∅)) := by
  rw [booleanSet_update_eq hE H i S, booleanSet_update_eq hE H i T]
  ext p
  simp only [Set.mem_sdiff, Set.mem_union, Set.mem_inter_iff]
  tauto

lemma booleanSet_mono {n : ℕ} {E : BooleanFunction n}
    (hE : IsMonotoneBooleanFunction E) {H G : Fin n → Set Point}
    (hHG : ∀ i, H i ⊆ G i) : booleanSet E H ⊆ booleanSet E G := by
  classical
  intro p hp
  apply hE _ _ ?_ hp
  intro i hi
  simp only [decide_eq_true_eq] at hi ⊢
  exact hHG i hi

def booleanCell {n : ℕ} (H : Fin n → Set Point) (P : Fin n → Bool) : Set Point :=
  ⋂ j, if P j then H j else (H j)ᶜ

def setMembershipPattern {n : ℕ} (H : Fin n → Set Point) (p : Point) : Fin n → Bool := by
  classical
  exact fun j ↦ decide (p ∈ H j)

lemma mem_booleanCell_iff {n : ℕ} (H : Fin n → Set Point) (P : Fin n → Bool)
    (p : Point) :
    p ∈ booleanCell H P ↔ setMembershipPattern H p = P := by
  classical
  simp only [booleanCell, Set.mem_iInter]
  constructor
  · intro hp
    funext j
    have hj := hp j
    cases hP : P j <;> simp [setMembershipPattern, hP] at hj ⊢ <;> exact hj
  · intro hp j
    have hj := congrFun hp j
    cases hP : P j <;> simp [setMembershipPattern, hP] at hj ⊢ <;> exact hj

lemma booleanSet_eq_iUnion_booleanCell {n : ℕ} (E : BooleanFunction n)
    (H : Fin n → Set Point) :
    booleanSet E H = ⋃ P : Fin n → Bool, if E P = true then booleanCell H P else ∅ := by
  classical
  ext p
  simp only [booleanSet, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_ite_empty_right]
  constructor
  · intro hp
    change E (setMembershipPattern H p) = true at hp
    refine ⟨setMembershipPattern H p, ?_, (mem_booleanCell_iff H _ p).mpr rfl⟩
    exact hp
  · rintro ⟨P, hEP, hp⟩
    have hpat := (mem_booleanCell_iff H P p).mp hp
    calc
      E (fun j ↦ decide (p ∈ H j)) = E (setMembershipPattern H p) := by
        congr 1
      _ = E P := congrArg E hpat
      _ = true := hEP

def closedBooleanCell {n : ℕ} (H : Fin n → PlanarHalfPlaneData)
    (P : Fin n → Bool) : Set Point :=
  ⋂ j, normalHalfPlane (H j).angle (H j).height
    (if P j then (H j).upper else !(H j).upper) false

lemma mem_booleanCell_iff_mem_closedBooleanCell_of_ne {n : ℕ}
    (H : Fin n → PlanarHalfPlaneData) (P : Fin n → Bool) (p : Point)
    (hp : ∀ j, inner ℝ p (normalVector (H j).angle) ≠ (H j).height) :
    p ∈ booleanCell (fun j ↦ (H j).carrier) P ↔ p ∈ closedBooleanCell H P := by
  simp only [booleanCell, closedBooleanCell, Set.mem_iInter]
  constructor <;> intro h j
  · have hj := h j
    have hne := hp j
    rcases lt_or_gt_of_ne hne with hlt | hgt <;>
      cases hP : P j <;> cases hu : (H j).upper <;> cases hs : (H j).strict <;>
      simp only [hP, hu, hs, PlanarHalfPlaneData.carrier, normalHalfPlane,
        Bool.false_eq_true, Bool.not_false, Bool.not_true, ↓reduceIte,
        Set.mem_compl_iff, Set.mem_ofPred_eq] at hj ⊢ <;> linarith
  · have hj := h j
    have hne := hp j
    rcases lt_or_gt_of_ne hne with hlt | hgt <;>
      cases hP : P j <;> cases hu : (H j).upper <;> cases hs : (H j).strict <;>
      simp only [hP, hu, hs, PlanarHalfPlaneData.carrier, normalHalfPlane,
        Bool.false_eq_true, Bool.not_false, Bool.not_true, ↓reduceIte,
        Set.mem_compl_iff, Set.mem_ofPred_eq] at hj ⊢ <;> linarith

def IsActiveBooleanPattern {n : ℕ} (E : BooleanFunction n) (i : Fin n)
    (P : Fin n → Bool) : Prop :=
  E (Function.update P i false) = false ∧
    E (Function.update P i true) = true

def activeBooleanPatterns {n : ℕ} (E : BooleanFunction n) (i : Fin n) :
    Finset (Fin n → Bool) := by
  classical
  exact Finset.univ.filter (IsActiveBooleanPattern E i)

def activeBooleanRegion {n : ℕ} (E : BooleanFunction n)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n) : Set Point :=
  booleanSet E (Function.update (fun j ↦ (H j).carrier) i Set.univ) \
    booleanSet E (Function.update (fun j ↦ (H j).carrier) i ∅)

lemma mem_activeBooleanRegion_iff {n : ℕ} (E : BooleanFunction n)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n) (p : Point) :
    p ∈ activeBooleanRegion E H i ↔
      IsActiveBooleanPattern E i (setMembershipPattern (fun j ↦ (H j).carrier) p) := by
  classical
  unfold activeBooleanRegion IsActiveBooleanPattern
  simp only [Set.mem_sdiff, booleanSet, Set.mem_ofPred_eq]
  have huniv : (fun j ↦ decide (p ∈ Function.update
      (fun j ↦ (H j).carrier) i Set.univ j)) =
      Function.update (setMembershipPattern (fun j ↦ (H j).carrier) p) i true := by
    funext j
    by_cases hji : j = i <;>
      simp [hji, Function.update_of_ne, setMembershipPattern]
  have hempty : (fun j ↦ decide (p ∈ Function.update
      (fun j ↦ (H j).carrier) i ∅ j)) =
      Function.update (setMembershipPattern (fun j ↦ (H j).carrier) p) i false := by
    funext j
    by_cases hji : j = i <;>
      simp [hji, Function.update_of_ne, setMembershipPattern]
  rw [huniv, hempty]
  cases hfalse : E (Function.update (setMembershipPattern
      (fun j ↦ (H j).carrier) p) i false) <;> simp

lemma measurableSet_planarHalfPlane_carrier (H : PlanarHalfPlaneData) :
    MeasurableSet H.carrier := by
  cases hu : H.upper <;> cases hs : H.strict <;>
    simp only [PlanarHalfPlaneData.carrier, normalHalfPlane, hu, hs,
      Bool.false_eq_true, ↓reduceIte] <;> measurability

lemma eventually_mem_carrier_iff_of_not_mem_boundaryLine (H : PlanarHalfPlaneData)
    (p : Point) (hp : p ∉ H.boundaryLine) :
    ∀ᶠ q in 𝓝 p, (q ∈ H.carrier ↔ p ∈ H.carrier) := by
  have hpne : inner ℝ p (normalVector H.angle) ≠ H.height := hp
  have hcont : Continuous (fun q : Point ↦ inner ℝ q (normalVector H.angle)) := by
    fun_prop
  rcases lt_or_gt_of_ne hpne with hplt | hpgt
  · have hev : ∀ᶠ q in 𝓝 p, inner ℝ q (normalVector H.angle) < H.height :=
      hcont.continuousAt.eventually_lt continuousAt_const hplt
    filter_upwards [hev] with q hq
    change (q ∈ normalHalfPlane H.angle H.height H.upper H.strict ↔
      p ∈ normalHalfPlane H.angle H.height H.upper H.strict)
    simp only [normalHalfPlane, Set.mem_ofPred_eq]
    cases H.upper <;> cases H.strict <;>
      simp only [Bool.false_eq_true, ↓reduceIte] <;>
      constructor <;> intro hm <;> linarith
  · have hev : ∀ᶠ q in 𝓝 p, H.height < inner ℝ q (normalVector H.angle) :=
      continuousAt_const.eventually_lt hcont.continuousAt hpgt
    filter_upwards [hev] with q hq
    change (q ∈ normalHalfPlane H.angle H.height H.upper H.strict ↔
      p ∈ normalHalfPlane H.angle H.height H.upper H.strict)
    simp only [normalHalfPlane, Set.mem_ofPred_eq]
    cases H.upper <;> cases H.strict <;>
      simp only [Bool.false_eq_true, ↓reduceIte] <;>
      constructor <;> intro hm <;> linarith

lemma eventually_setMembershipPattern_eq_of_ne {n : ℕ}
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n) (p : Point)
    (hp : ∀ j, j ≠ i → p ∉ (H j).boundaryLine) :
    ∀ᶠ q in 𝓝 p, ∀ j, j ≠ i →
      setMembershipPattern (fun k ↦ (H k).carrier) q j =
        setMembershipPattern (fun k ↦ (H k).carrier) p j := by
  suffices ∀ᶠ q in 𝓝 p, ∀ j ∈ (Set.univ : Set (Fin n)), j ≠ i →
      setMembershipPattern (fun k ↦ (H k).carrier) q j =
        setMembershipPattern (fun k ↦ (H k).carrier) p j by
    exact this.mono fun q hq j ↦ hq j (Set.mem_univ j)
  apply (Filter.eventually_all_finite Set.finite_univ).2
  intro j _
  by_cases hji : j = i
  · exact Filter.Eventually.of_forall fun _ hj ↦ (hj hji).elim
  · filter_upwards [eventually_mem_carrier_iff_of_not_mem_boundaryLine (H j) p
      (hp j hji)] with q hq
    intro _
    simp only [setMembershipPattern]
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using hq

lemma measurableSet_booleanCell {n : ℕ} (H : Fin n → PlanarHalfPlaneData)
    (P : Fin n → Bool) :
    MeasurableSet (booleanCell (fun j ↦ (H j).carrier) P) := by
  apply MeasurableSet.iInter
  intro j
  cases hP : P j
  · simpa [booleanCell, hP] using (measurableSet_planarHalfPlane_carrier (H j)).compl
  · simpa [booleanCell, hP] using measurableSet_planarHalfPlane_carrier (H j)

lemma measurableSet_booleanSet {n : ℕ} (E : BooleanFunction n)
    (H : Fin n → PlanarHalfPlaneData) :
    MeasurableSet (booleanSet E (fun j ↦ (H j).carrier)) := by
  rw [booleanSet_eq_iUnion_booleanCell]
  apply MeasurableSet.iUnion
  intro P
  by_cases hP : E P = true
  · simpa [hP] using measurableSet_booleanCell H P
  · simp [hP]

lemma monotoneBoolean_update_false_true {n : ℕ} {E : BooleanFunction n}
    (hE : IsMonotoneBooleanFunction E) (i : Fin n) (P : Fin n → Bool) :
    E (Function.update P i false) = true →
      E (Function.update P i true) = true := by
  intro htrue
  apply hE _ _ _ htrue
  intro j hj
  by_cases hji : j = i
  · subst j
    simp
  · simpa [Function.update_of_ne hji] using hj

lemma not_isActiveBooleanPattern_iff {n : ℕ} {E : BooleanFunction n}
    (hE : IsMonotoneBooleanFunction E) (i : Fin n) (P : Fin n → Bool) :
    ¬IsActiveBooleanPattern E i P ↔
      E (Function.update P i false) = E (Function.update P i true) := by
  unfold IsActiveBooleanPattern
  constructor
  · intro hnot
    cases hf : E (Function.update P i false) <;>
      cases ht : E (Function.update P i true)
    · rfl
    · exact (hnot ⟨hf, ht⟩).elim
    · have hcontra := monotoneBoolean_update_false_true hE i P hf
      rw [ht] at hcontra
      exact (Bool.false_ne_true hcontra).elim
    · rfl
  · intro heq hactive
    rw [hactive.1, hactive.2] at heq
    exact Bool.false_ne_true heq

end MovingSofa.Nef
