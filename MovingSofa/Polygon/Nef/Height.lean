import MovingSofa.Polygon.Nef.Cells
import MovingSofa.Classical.Area

noncomputable section

namespace MovingSofa

def perturbNefHeight {n : ℕ} (E : BooleanFunction n)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n) (δ : ℝ) : Set Point :=
  booleanSet E (fun j ↦
    (if j = i then { H j with height := (H j).height + δ } else H j).carrier)

end MovingSofa

namespace MovingSofa.Nef

open Filter Topology

lemma perturbNefHeight_eq_update {n : ℕ} (E : BooleanFunction n)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n) (δ : ℝ) :
    perturbNefHeight E H i δ = booleanSet E
      (Function.update (fun j ↦ (H j).carrier) i
        ({ H i with height := (H i).height + δ }).carrier) := by
  unfold perturbNefHeight
  congr 1
  funext j
  by_cases hji : j = i <;> simp [hji, Function.update_of_ne]

lemma perturbNefHeight_sdiff {n : ℕ} {E : BooleanFunction n}
    (hE : IsMonotoneBooleanFunction E) (H : Fin n → PlanarHalfPlaneData)
    (i : Fin n) (δ ε : ℝ) :
    perturbNefHeight E H i δ \ perturbNefHeight E H i ε =
      (({ H i with height := (H i).height + δ }).carrier \
        ({ H i with height := (H i).height + ε }).carrier) ∩
        (booleanSet E (Function.update (fun j ↦ (H j).carrier) i Set.univ) \
          booleanSet E (Function.update (fun j ↦ (H j).carrier) i ∅)) := by
  rw [perturbNefHeight_eq_update, perturbNefHeight_eq_update]
  exact booleanSet_update_sdiff hE _ _ _ _

def heightInterval (strict : Bool) (h δ ε : ℝ) : Set ℝ :=
  if strict then Set.Ico (h + ε) (h + δ) else Set.Ioc (h + ε) (h + δ)

lemma measurableSet_heightInterval (strict : Bool) (h δ ε : ℝ) :
    MeasurableSet (heightInterval strict h δ ε) := by
  cases strict <;> simp [heightInterval]

lemma integral_heightInterval_eq_intervalIntegral (strict : Bool)
    (h δ ε : ℝ) (f : ℝ → ℝ) (hεδ : ε ≤ δ) :
    (∫ x in heightInterval strict h δ ε, f x) =
      ∫ x in h + ε..h + δ, f x := by
  have hle : h + ε ≤ h + δ := by linarith
  cases strict
  · simp only [heightInterval, Bool.false_eq_true, ↓reduceIte]
    exact (intervalIntegral.integral_of_le hle).symm
  · simp only [heightInterval, ↓reduceIte]
    rw [MeasureTheory.integral_Ico_eq_integral_Ioc]
    exact (intervalIntegral.integral_of_le hle).symm

lemma mem_heightInterval_bounds {strict : Bool} {h δ ε x : ℝ}
    (hx : x ∈ heightInterval strict h δ ε) :
    h + ε ≤ x ∧ x ≤ h + δ := by
  cases strict <;> simp [heightInterval] at hx <;>
    constructor <;> linarith [hx.1, hx.2]

lemma carrier_sdiff_carrier_eq_heightInterval (H : PlanarHalfPlaneData)
    (hSide : H.upper = false) (δ ε : ℝ) :
    ({ H with height := H.height + δ }).carrier \
        ({ H with height := H.height + ε }).carrier =
      {p | inner ℝ p (normalVector H.angle) ∈
        heightInterval H.strict H.height δ ε} := by
  ext p
  cases hs : H.strict <;>
    simp [PlanarHalfPlaneData.carrier, normalHalfPlane, hSide,
      heightInterval] <;> tauto

lemma perturbNefHeight_sdiff_eq_heightInterval {n : ℕ}
    {E : BooleanFunction n} (hE : IsMonotoneBooleanFunction E)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n)
    (hSide : (H i).upper = false) (δ ε : ℝ) :
    perturbNefHeight E H i δ \ perturbNefHeight E H i ε =
      {p | inner ℝ p (normalVector (H i).angle) ∈
        heightInterval (H i).strict (H i).height δ ε} ∩
        (booleanSet E (Function.update (fun j ↦ (H j).carrier) i Set.univ) \
          booleanSet E (Function.update (fun j ↦ (H j).carrier) i ∅)) := by
  rw [perturbNefHeight_sdiff hE H i δ ε,
    carrier_sdiff_carrier_eq_heightInterval (H i) hSide]

lemma perturbNefHeight_mono {n : ℕ} {E : BooleanFunction n}
    (hE : IsMonotoneBooleanFunction E) (H : Fin n → PlanarHalfPlaneData)
    (i : Fin n) (hSide : (H i).upper = false) :
    Monotone (perturbNefHeight E H i) := by
  intro δ ε hδε
  apply booleanSet_mono hE
  intro j p hp
  by_cases hji : j = i
  · subst j
    simp only at hp ⊢
    change p ∈ normalHalfPlane (H i).angle ((H i).height + δ) (H i).upper
      (H i).strict at hp
    change p ∈ normalHalfPlane (H i).angle ((H i).height + ε) (H i).upper
      (H i).strict
    cases hstrict : (H i).strict <;>
      simp only [normalHalfPlane, hSide, hstrict, Bool.false_eq_true, ite_false,
        ite_true, Set.mem_ofPred_eq] at hp ⊢
    · exact hp.trans (add_le_add_right hδε _)
    · exact hp.trans_le (add_le_add_right hδε _)
  · simpa only [ite_eq_right hji] using hp

lemma measurableSet_perturbNefHeight {n : ℕ} (E : BooleanFunction n)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n) (δ : ℝ) :
    MeasurableSet (perturbNefHeight E H i δ) := by
  unfold perturbNefHeight
  apply measurableSet_booleanSet

lemma area_perturb_sub_eq_volume_sdiff {n : ℕ} {E : BooleanFunction n}
    (hE : IsMonotoneBooleanFunction E) (H : Fin n → PlanarHalfPlaneData)
    (i : Fin n) (hSide : (H i).upper = false) (R ε₀ δ ε : ℝ)
    (hεδ : ε ≤ δ) (hδ : |δ| ≤ ε₀) (hε : |ε| ≤ ε₀)
    (hBound : ∀ z : ℝ, |z| ≤ ε₀ →
      perturbNefHeight E H i z ⊆ Metric.closedBall 0 R) :
    ClassicalResults.area (perturbNefHeight E H i δ) -
        ClassicalResults.area (perturbNefHeight E H i ε) =
      (MeasureTheory.volume
        (perturbNefHeight E H i δ \ perturbNefHeight E H i ε)).toReal := by
  have hmono := perturbNefHeight_mono hE H i hSide hεδ
  have hfiniteδ : MeasureTheory.volume (perturbNefHeight E H i δ) ≠ ⊤ := by
    apply ne_of_lt
    exact lt_of_le_of_lt (MeasureTheory.measure_mono (hBound δ hδ))
      MeasureTheory.measure_closedBall_lt_top
  have hfiniteε : MeasureTheory.volume (perturbNefHeight E H i ε) ≠ ⊤ := by
    apply ne_of_lt
    exact lt_of_le_of_lt (MeasureTheory.measure_mono (hBound ε hε))
      MeasureTheory.measure_closedBall_lt_top
  rw [ClassicalResults.area, ClassicalResults.area,
    ← ENNReal.toReal_sub_of_le (MeasureTheory.measure_mono hmono) hfiniteδ,
    ← MeasureTheory.measure_sdiff hmono
      (measurableSet_perturbNefHeight E H i ε).nullMeasurableSet hfiniteε]

lemma perturbNefHeight_zero {n : ℕ} (E : BooleanFunction n)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n) :
    perturbNefHeight E H i 0 = booleanSet E (fun j ↦ (H j).carrier) := by
  ext p
  simp [perturbNefHeight, PlanarHalfPlaneData.carrier]

end MovingSofa.Nef
