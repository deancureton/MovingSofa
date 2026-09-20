import MovingSofa.Gerver.PaperSet
import MovingSofa.Geometry.Parallelogram
import MovingSofa.Geometry.Frame
import MovingSofa.Gerver.DirectRegularity

noncomputable section

namespace MovingSofa

def gerverOuterCap : Set Point :=
  {q | 0 ≤ q 1 ∧ ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
    inner ℝ q (normalVector (t : Real.Angle)) ≤
      inner ℝ (paperGerverPath t) (normalVector (t : Real.Angle)) + 1 ∧
    inner ℝ q (tangentVector (t : Real.Angle)) ≤
      inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) + 1}

def gerverLiteralNiche : Set Point :=
  {q | 0 ≤ q 1 ∧ ∃ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
    inner ℝ (q - paperGerverPath t) (normalVector (t : Real.Angle)) < 0 ∧
    inner ℝ (q - paperGerverPath t) (tangentVector (t : Real.Angle)) < 0}

def gerverLiteralSofa : Set Point := gerverOuterCap \ gerverLiteralNiche

def gerverLiteralSets : Set Point × Set Point := (gerverLiteralNiche, gerverLiteralSofa)

/-- The paper outer cap is the coordinate transport of the certified Romik cap `K₀`. -/
theorem mem_gerverOuterCap_iff (q : Point) :
    q ∈ gerverOuterCap ↔
      GerverSofa.PartF.Coordinates.fromPlane q ∈
        GerverSofa.Romik.K0 GerverSofa.PartB.params := by
  simp only [gerverOuterCap, Set.mem_ofPred_eq, GerverSofa.Romik.mem_K0, Set.mem_inter_iff,
    GerverSofa.Romik.mem_supportHalfU, GerverSofa.Romik.mem_supportHalfV,
    inner_normalVector_eq_dot, inner_tangentVector_eq_dot]
  exact Iff.rfl

/-- A point whose coordinate pair lies in the certified Romik cap `K₀` lies in the paper
outer cap. -/
theorem toPlane_mem_gerverOuterCap {x : GerverSofa.Point}
    (hx : x ∈ GerverSofa.Romik.K0 GerverSofa.PartB.params) :
    GerverSofa.PartF.Coordinates.toPlane x ∈ gerverOuterCap :=
  (mem_gerverOuterCap_iff _).2 (by rwa [GerverSofa.PartF.Coordinates.fromPlane_toPlane])

/-- The paper literal niche is the coordinate transport of the certified Romik niche. -/
theorem mem_gerverLiteralNiche_iff (q : Point) :
    q ∈ gerverLiteralNiche ↔
      GerverSofa.PartF.Coordinates.fromPlane q ∈
        GerverSofa.Romik.niche GerverSofa.PartB.params := by
  have hsub : ∀ (r : Point) (t : ℝ),
      GerverSofa.PartF.Coordinates.fromPlane (r - paperGerverPath t) =
        ((GerverSofa.PartF.Coordinates.fromPlane r).1 -
            (GerverSofa.Romik.path GerverSofa.PartB.params t).1,
          (GerverSofa.PartF.Coordinates.fromPlane r).2 -
            (GerverSofa.Romik.path GerverSofa.PartB.params t).2) := fun _ _ => rfl
  constructor
  · rintro ⟨hy, t, ht, h1, h2⟩
    rw [inner_normalVector_eq_dot, hsub] at h1
    rw [inner_tangentVector_eq_dot, hsub] at h2
    exact ⟨hy, t, ht, h1, h2⟩
  · rintro ⟨hy, t, ht, h1, h2⟩
    refine ⟨hy, t, ht, ?_, ?_⟩
    · rw [inner_normalVector_eq_dot, hsub]; exact h1
    · rw [inner_tangentVector_eq_dot, hsub]; exact h2

theorem paperGerverSofa_eq_literal : paperGerverSofa = gerverLiteralSofa := by
  have hTpos : (0 : ℝ) < Real.pi / 2 := by positivity
  have hmemhall : ∀ (t : Real.Angle) (v q : Point),
      q ∈ (fun p ↦ rotationMap t p + v) '' hallway ↔
        (inner ℝ (q - v) (normalVector t) ≤ 1 ∧
          inner ℝ (q - v) (tangentVector t) ≤ 1) ∧
        (0 ≤ inner ℝ (q - v) (normalVector t) ∨
          0 ≤ inner ℝ (q - v) (tangentVector t)) := by
    intro t v q
    constructor
    · rintro ⟨p, hp, rfl⟩
      have h0 : inner ℝ (rotationMap t p + v - v) (normalVector t) = p 0 := by
        rw [add_sub_cancel_right, inner_rotationMap_normalVector]
      have h1 : inner ℝ (rotationMap t p + v - v) (tangentVector t) = p 1 := by
        rw [add_sub_cancel_right, inner_rotationMap_tangentVector]
      simp only [h0, h1]
      exact (mem_hallway_iff p).1 hp
    · intro h
      obtain ⟨p, hp⟩ := (EuclideanGeometry.o.rotation t).surjective (q - v)
      have hpq : rotationMap t p = q - v := hp
      have h0 : p 0 = inner ℝ (q - v) (normalVector t) := by
        rw [← inner_rotationMap_normalVector p t, hpq]
      have h1 : p 1 = inner ℝ (q - v) (tangentVector t) := by
        rw [← inner_rotationMap_tangentVector p t, hpq]
      refine ⟨p, (mem_hallway_iff p).2 ?_, ?_⟩
      · rw [h0, h1]; exact h
      · show rotationMap t p + v = q
        rw [hpq]; abel
  have hconttan : Continuous (fun t : ℝ ↦ tangentVector (t : Real.Angle)) := by
    let c : ℝ → (i : Fin 2) → ℝ :=
      fun t i ↦ Fin.cases (-Real.sin t) (fun _ ↦ Real.cos t) i
    have hc : Continuous c := by
      apply continuous_pi
      intro i
      fin_cases i
      · exact Real.continuous_sin.neg
      · exact Real.continuous_cos
    have heq : (fun t : ℝ ↦ tangentVector (t : Real.Angle)) =
        (fun t ↦ WithLp.toLp 2 (c t)) := by
      funext t
      ext i
      fin_cases i <;> rfl
    rw [heq]
    exact (PiLp.continuous_toLp (2 : ENNReal) (fun _ : Fin 2 ↦ ℝ)).comp hc
  have hreg := gerver_direct_path_regularity GerverSofa.PartB.params
    GerverSofa.PartB.params_mem GerverSofa.PartB.params_equations
  have hpathcont : Continuous paperGerverPath :=
    GerverSofa.PartF.Coordinates.continuous_toPlane.comp hreg.1.continuous
  have hpath0 : paperGerverPath 0 = 0 := by
    show GerverSofa.PartF.Coordinates.toPlane
      (GerverSofa.Romik.path GerverSofa.PartB.params 0) = 0
    rw [hreg.2.1]
    ext i
    fin_cases i <;> rfl
  have hstrip : ∀ q : Point,
      q ∈ (strips (Real.pi / 2)).1 ∩ (strips (Real.pi / 2)).2.2 ↔ 0 ≤ q 1 ∧ q 1 ≤ 1 := by
    intro q
    have h := mem_stripParallelogram_iff (Real.pi / 2) q
    rw [inner_normalVector_pi_div_two] at h
    have hset : (strips (Real.pi / 2)).1 ∩ (strips (Real.pi / 2)).2.2 =
        (stripParallelogram (Real.pi / 2)).1 := rfl
    rw [hset, h]
    tauto
  have hshift : ∀ w z n : Point,
      (inner ℝ w n ≤ inner ℝ z n + 1 ↔ inner ℝ (w - z) n ≤ 1) := by
    intro w z n
    rw [inner_sub_left]
    constructor <;> intro h <;> linarith
  ext q
  constructor
  · rintro ⟨hs, hint⟩
    have hhall : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
        (inner ℝ (q - paperGerverPath t) (normalVector (t : Real.Angle)) ≤ 1 ∧
          inner ℝ (q - paperGerverPath t) (tangentVector (t : Real.Angle)) ≤ 1) ∧
        (0 ≤ inner ℝ (q - paperGerverPath t) (normalVector (t : Real.Angle)) ∨
          0 ≤ inner ℝ (q - paperGerverPath t) (tangentVector (t : Real.Angle))) := fun t ht ↦
      (hmemhall _ _ _).1 (Set.mem_iInter₂.1 hint t ht)
    refine ⟨⟨((hstrip q).1 hs).1, fun t ht ↦
      ⟨(hshift _ _ _).2 (hhall t ht).1.1, (hshift _ _ _).2 (hhall t ht).1.2⟩⟩, ?_⟩
    rintro ⟨-, t, ht, hlt1, hlt2⟩
    rcases (hhall t (Set.Ioo_subset_Icc_self ht)).2 with h | h
    · linarith
    · linarith
  · rintro ⟨⟨hy, hcap⟩, hniche⟩
    have hcap' : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
        inner ℝ (q - paperGerverPath t) (normalVector (t : Real.Angle)) ≤ 1 ∧
        inner ℝ (q - paperGerverPath t) (tangentVector (t : Real.Angle)) ≤ 1 := fun t ht ↦
      ⟨(hshift _ _ _).1 (hcap t ht).1, (hshift _ _ _).1 (hcap t ht).2⟩
    have hopen : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        0 ≤ inner ℝ (q - paperGerverPath t) (normalVector (t : Real.Angle)) ∨
        0 ≤ inner ℝ (q - paperGerverPath t) (tangentVector (t : Real.Angle)) := by
      intro t ht
      by_contra hcon
      exact hniche ⟨hy, t, ht, not_le.mp fun h ↦ hcon (Or.inl h),
        not_le.mp fun h ↦ hcon (Or.inr h)⟩
    have hclosed : IsClosed {t : ℝ |
        0 ≤ max (inner ℝ (q - paperGerverPath t) (normalVector (t : Real.Angle)))
          (inner ℝ (q - paperGerverPath t) (tangentVector (t : Real.Angle)))} :=
      isClosed_le continuous_const
        (((continuous_const.sub hpathcont).inner continuous_normalVector_real).max
          ((continuous_const.sub hpathcont).inner hconttan))
    have hIcc : Set.Icc (0 : ℝ) (Real.pi / 2) ⊆ {t : ℝ |
        0 ≤ max (inner ℝ (q - paperGerverPath t) (normalVector (t : Real.Angle)))
          (inner ℝ (q - paperGerverPath t) (tangentVector (t : Real.Angle)))} := by
      rw [← closure_Ioo (ne_of_lt hTpos)]
      exact hclosed.closure_subset_iff.mpr fun t ht ↦ le_max_iff.mpr (hopen t ht)
    have hy1 : q 1 ≤ 1 := by
      have h := (hcap' 0 (Set.left_mem_Icc.mpr hTpos.le)).2
      rwa [hpath0, sub_zero, inner_tangentVector_zero] at h
    refine ⟨(hstrip q).2 ⟨hy, hy1⟩, Set.mem_iInter₂.2 fun t ht ↦ ?_⟩
    exact (hmemhall _ _ _).2
      ⟨hcap' t ht, le_max_iff.mp (hIcc ht)⟩

end MovingSofa
