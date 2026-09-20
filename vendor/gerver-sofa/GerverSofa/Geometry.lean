import GerverSofa.Systems
import GerverSofa.SupportingHallway

/-!
# Concrete Gerver cap, niche and fixed sofa

The definitions follow the manuscript literally.  This file also proves the
closedness part of the main topological certificate directly from the
half-plane definitions; it does not use the numerical certificate or Baek's
cap theory.
-/

noncomputable section

namespace GerverSofa

/-- Euclidean scalar product in the fixed coordinate representation. -/
def dot (p q : Point) : ℝ := p.1 * q.1 + p.2 * q.2

/-- Rotating outer-wall normals. -/
def u (t : ℝ) : Point := (Real.cos t, Real.sin t)
def v (t : ℝ) : Point := (-Real.sin t, Real.cos t)

/-- The lower fan in the manuscript normalisation. -/
def capFan : Set Point := {q | 0 ≤ q.2}

/-- First rotating supporting half-plane. -/
def supportHalfU (p : Romik.Params) (t : ℝ) : Set Point :=
  {q | dot q (u t) ≤ dot (Romik.path p t) (u t) + 1}

/-- Second rotating supporting half-plane. -/
def supportHalfV (p : Romik.Params) (t : ℝ) : Set Point :=
  {q | dot q (v t) ≤ dot (Romik.path p t) (v t) + 1}

/-- The cap `K₀` reconstructed from the five-phase path. -/
def Romik.K0 (p : Romik.Params) : Set Point :=
  {q | 0 ≤ q.2 ∧
    ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      q ∈ supportHalfU p t ∩ supportHalfV p t}

/-- Open inner quadrant of the supporting hallway at physical angle `t`. -/
def Romik.innerQuadrantAt (p : Romik.Params) (t : ℝ) : Set Point :=
  let x := Romik.path p t
  {q | dot (q.1 - x.1, q.2 - x.2) (u t) < 0 ∧
       dot (q.1 - x.1, q.2 - x.2) (v t) < 0}

/-- Union of all forbidden inner quadrants at interior rotation times. -/
def Romik.innerUnion (p : Romik.Params) : Set Point :=
  {q | ∃ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), q ∈ Romik.innerQuadrantAt p t}

/-- The niche removed from the cap. -/
def Romik.niche (p : Romik.Params) : Set Point :=
  capFan ∩ Romik.innerUnion p

/-- The fixed Gerver candidate `G = K₀ \ N(K₀)`. -/
def Romik.sofa (p : Romik.Params) : Set Point :=
  Romik.K0 p \ Romik.niche p

/-- Physical supporting hallway at normalized time `s`. -/
def Romik.hallwayAt (p : Romik.Params) (s : ℝ) : Set Point :=
  supportingHallway (Romik.frame p s)

/-! ## Closedness facts independent of the numerical certificate -/

private theorem continuous_dot_fixed (a : Point) :
    Continuous (fun q : Point => dot q a) := by
  unfold dot
  fun_prop

private theorem continuous_shifted_dot (x a : Point) :
    Continuous (fun q : Point => dot (q.1 - x.1, q.2 - x.2) a) := by
  unfold dot
  fun_prop

/-- A fixed supporting half-plane is closed. -/
theorem isClosed_supportHalfU (p : Romik.Params) (t : ℝ) :
    IsClosed (supportHalfU p t) := by
  change IsClosed ((fun q : Point => dot q (u t)) ⁻¹'
    Set.Iic (dot (Romik.path p t) (u t) + 1))
  exact isClosed_Iic.preimage (continuous_dot_fixed (u t))

/-- The other fixed supporting half-plane is closed. -/
theorem isClosed_supportHalfV (p : Romik.Params) (t : ℝ) :
    IsClosed (supportHalfV p t) := by
  change IsClosed ((fun q : Point => dot q (v t)) ⁻¹'
    Set.Iic (dot (Romik.path p t) (v t) + 1))
  exact isClosed_Iic.preimage (continuous_dot_fixed (v t))

/-- The fan constraint is closed. -/
theorem isClosed_capFan : IsClosed capFan := by
  change IsClosed ((fun q : Point => q.2) ⁻¹' Set.Ici 0)
  exact isClosed_Ici.preimage continuous_snd

/-- The bounded-quantifier definition of `K₀` as an explicit intersection. -/
theorem Romik.K0_eq_inter_iInter (p : Romik.Params) :
    Romik.K0 p = capFan ∩
      ⋂ t : {t : ℝ // t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)},
        (supportHalfU p t.1 ∩ supportHalfV p t.1) := by
  ext q
  constructor
  · rintro ⟨hbase, hall⟩
    refine ⟨hbase, Set.mem_iInter.mpr ?_⟩
    intro t
    exact hall t.1 t.2
  · rintro ⟨hbase, hall⟩
    refine ⟨hbase, ?_⟩
    intro t ht
    exact Set.mem_iInter.mp hall ⟨t, ht⟩

/-- `K₀` is closed, before any support-maximisation or compactness argument. -/
theorem Romik.isClosed_K0 (p : Romik.Params) : IsClosed (Romik.K0 p) := by
  rw [Romik.K0_eq_inter_iInter]
  exact isClosed_capFan.inter <|
    isClosed_iInter fun t =>
      (isClosed_supportHalfU p t.1).inter (isClosed_supportHalfV p t.1)

/-- Every instantaneous inner quadrant is open. -/
theorem Romik.isOpen_innerQuadrantAt (p : Romik.Params) (t : ℝ) :
    IsOpen (Romik.innerQuadrantAt p t) := by
  let x := Romik.path p t
  have hu : IsOpen
      ((fun q : Point => dot (q.1 - x.1, q.2 - x.2) (u t)) ⁻¹' Set.Iio 0) :=
    isOpen_Iio.preimage (continuous_shifted_dot x (u t))
  have hv : IsOpen
      ((fun q : Point => dot (q.1 - x.1, q.2 - x.2) (v t)) ⁻¹' Set.Iio 0) :=
    isOpen_Iio.preimage (continuous_shifted_dot x (v t))
  change IsOpen
    (((fun q : Point => dot (q.1 - x.1, q.2 - x.2) (u t)) ⁻¹' Set.Iio 0) ∩
     ((fun q : Point => dot (q.1 - x.1, q.2 - x.2) (v t)) ⁻¹' Set.Iio 0))
  exact hu.inter hv

/-- The union of all interior-time inner quadrants is open. -/
theorem Romik.isOpen_innerUnion (p : Romik.Params) :
    IsOpen (Romik.innerUnion p) := by
  have hrepr : Romik.innerUnion p =
      ⋃ t : {t : ℝ // t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)},
        Romik.innerQuadrantAt p t.1 := by
    ext q
    constructor
    · rintro ⟨t, ht, hq⟩
      exact Set.mem_iUnion.mpr ⟨⟨t, ht⟩, hq⟩
    · intro hq
      rcases Set.mem_iUnion.mp hq with ⟨t, hq⟩
      exact ⟨t.1, t.2, hq⟩
  rw [hrepr]
  exact isOpen_iUnion fun t => Romik.isOpen_innerQuadrantAt p t.1

/-- The cap lies in its fan by definition. -/
theorem Romik.K0_subset_capFan (p : Romik.Params) : Romik.K0 p ⊆ capFan := by
  intro q hq
  exact hq.1

/-- Since `K₀ ⊆ capFan`, removing the niche is the same as removing the open
union of forbidden quadrants. -/
theorem Romik.sofa_eq_K0_diff_innerUnion (p : Romik.Params) :
    Romik.sofa p = Romik.K0 p \ Romik.innerUnion p := by
  ext q
  constructor
  · rintro ⟨hqK, hqN⟩
    refine ⟨hqK, ?_⟩
    intro hqU
    exact hqN ⟨Romik.K0_subset_capFan p hqK, hqU⟩
  · rintro ⟨hqK, hqU⟩
    refine ⟨hqK, ?_⟩
    rintro ⟨_hqFan, hqInner⟩
    exact hqU hqInner

/-- The concrete fixed sofa candidate is closed for every parameter vector. -/
theorem Romik.isClosed_sofa (p : Romik.Params) : IsClosed (Romik.sofa p) := by
  rw [Romik.sofa_eq_K0_diff_innerUnion]
  simpa [Set.diff_eq] using
    (Romik.isClosed_K0 p).inter (Romik.isOpen_innerUnion p).isClosed_compl

end GerverSofa

namespace GerverSofa

/-! ## Algebraic hallway characterisation and endpoint assembly -/

@[simp] theorem Romik.mem_supportHalfU (p : Romik.Params) (t : ℝ) (q : Point) :
    q ∈ supportHalfU p t ↔
      dot q (u t) ≤ dot (Romik.path p t) (u t) + 1 := Iff.rfl

@[simp] theorem Romik.mem_supportHalfV (p : Romik.Params) (t : ℝ) (q : Point) :
    q ∈ supportHalfV p t ↔
      dot q (v t) ≤ dot (Romik.path p t) (v t) + 1 := Iff.rfl

@[simp] theorem Romik.mem_K0 (p : Romik.Params) (q : Point) :
    q ∈ Romik.K0 p ↔
      0 ≤ q.2 ∧
      ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
        q ∈ supportHalfU p t ∩ supportHalfV p t := Iff.rfl

@[simp] theorem Romik.mem_innerUnion (p : Romik.Params) (q : Point) :
    q ∈ Romik.innerUnion p ↔
      ∃ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        q ∈ Romik.innerQuadrantAt p t := Iff.rfl

@[simp] theorem Romik.mem_niche (p : Romik.Params) (q : Point) :
    q ∈ Romik.niche p ↔ q ∈ capFan ∧ q ∈ Romik.innerUnion p := Iff.rfl

@[simp] theorem Romik.mem_sofa (p : Romik.Params) (q : Point) :
    q ∈ Romik.sofa p ↔ q ∈ Romik.K0 p ∧ q ∉ Romik.niche p := Iff.rfl

/-- The inverse supporting frame has exactly the two signed wall coordinates
used in the manuscript. -/
theorem Romik.frame_inv_act_formula (p : Romik.Params) (s : ℝ) (q : Point) :
    (Romik.frame p s).inv.act q =
      (dot (q.1 - (Romik.path p (Romik.angle s)).1,
            q.2 - (Romik.path p (Romik.angle s)).2) (u (Romik.angle s)),
       dot (q.1 - (Romik.path p (Romik.angle s)).1,
            q.2 - (Romik.path p (Romik.angle s)).2) (v (Romik.angle s))) := by
  apply Prod.ext <;>
    simp [Romik.frame, SE2.inv, SE2.act, dot, u, v] <;> ring

/-- A point is in the supporting hallway iff its two wall coordinates lie in
`Q⁺` but not simultaneously in the open inner quadrant `Q⁻`. -/
theorem Romik.mem_hallwayAt_iff_wall_coordinates
    (p : Romik.Params) (s : ℝ) (q : Point) :
    q ∈ Romik.hallwayAt p s ↔
      let t := Romik.angle s
      let x := Romik.path p t
      (dot (q.1 - x.1, q.2 - x.2) (u t) ≤ 1 ∧
       dot (q.1 - x.1, q.2 - x.2) (v t) ≤ 1) ∧
      ¬ (dot (q.1 - x.1, q.2 - x.2) (u t) < 0 ∧
         dot (q.1 - x.1, q.2 - x.2) (v t) < 0) := by
  rw [Romik.hallwayAt, mem_supportingHallway_iff]
  rw [Romik.frame_inv_act_formula]
  rw [hallway_eq_outer_diff_inner]
  simp [outerQuarter, innerQuarter]

/-- A sofa point cannot lie in an instantaneous forbidden quadrant at an
interior physical time. -/
theorem Romik.not_mem_innerQuadrantAt_of_mem_sofa
    (p : Romik.Params) {q : Point} (hq : q ∈ Romik.sofa p)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    q ∉ Romik.innerQuadrantAt p t := by
  intro hinner
  exact hq.2 ⟨Romik.K0_subset_capFan p hq.1, ⟨t, ht, hinner⟩⟩

/-- The lower-fan constraint excludes the initial inner quadrant once the
physical path starts at the origin. -/
theorem Romik.not_mem_initial_innerQuadrant
    (p : Romik.Params) (hzero : Romik.path p 0 = (0, 0))
    {q : Point} (hq : q ∈ Romik.sofa p) :
    q ∉ Romik.innerQuadrantAt p 0 := by
  intro hinner
  have hbase : 0 ≤ q.2 := hq.1.1
  have hneg : q.2 < 0 := by
    simpa [Romik.innerQuadrantAt, dot, u, v, hzero] using hinner.2
  exact (not_lt_of_ge hbase) hneg

/-- The lower-fan constraint excludes the final inner quadrant once the final
path point has second coordinate zero. -/
theorem Romik.not_mem_final_innerQuadrant
    (p : Romik.Params)
    (hend : (Romik.path p (Real.pi / 2)).2 = 0)
    {q : Point} (hq : q ∈ Romik.sofa p) :
    q ∉ Romik.innerQuadrantAt p (Real.pi / 2) := by
  intro hinner
  have hbase : 0 ≤ q.2 := hq.1.1
  have hneg : q.2 < 0 := by
    simpa [Romik.innerQuadrantAt, dot, u, v, hend] using hinner.1
  exact (not_lt_of_ge hbase) hneg

/-- The concrete cap-minus-niche set lies in every supporting hallway.  The
only endpoint input is the pair of path normalisations used in the paper. -/
theorem Romik.sofa_subset_hallwayAt
    (p : Romik.Params)
    (hzero : Romik.path p 0 = (0, 0))
    (hend : (Romik.path p (Real.pi / 2)).2 = 0) :
    ∀ s ∈ Set.Icc (0 : ℝ) 1,
      Romik.sofa p ⊆ Romik.hallwayAt p s := by
  intro s hs q hq
  rw [Romik.mem_hallwayAt_iff_wall_coordinates]
  dsimp only
  have hangle : Romik.angle s ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
    constructor
    · exact mul_nonneg hs.1 (by positivity)
    · have hm := mul_le_mul_of_nonneg_right hs.2
          (show 0 ≤ Real.pi / 2 by positivity)
      simpa [Romik.angle] using hm
  have hsupports := hq.1.2 (Romik.angle s) hangle
  constructor
  · constructor
    · have hu := hsupports.1
      change dot q (u (Romik.angle s)) ≤
        dot (Romik.path p (Romik.angle s)) (u (Romik.angle s)) + 1 at hu
      dsimp [dot] at hu ⊢
      linarith
    · have hv := hsupports.2
      change dot q (v (Romik.angle s)) ≤
        dot (Romik.path p (Romik.angle s)) (v (Romik.angle s)) + 1 at hv
      dsimp [dot] at hv ⊢
      linarith
  · change q ∉ Romik.innerQuadrantAt p (Romik.angle s)
    by_cases hs0 : s = 0
    · subst s
      simpa using Romik.not_mem_initial_innerQuadrant p hzero hq
    by_cases hs1 : s = 1
    · subst s
      simpa using Romik.not_mem_final_innerQuadrant p hend hq
    · have hsIoo : s ∈ Set.Ioo (0 : ℝ) 1 := by
        exact ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0),
          lt_of_le_of_ne hs.2 hs1⟩
      have hangleIoo : Romik.angle s ∈
          Set.Ioo (0 : ℝ) (Real.pi / 2) := by
        constructor
        · exact mul_pos hsIoo.1 (by positivity)
        · have hm := mul_lt_mul_of_pos_right hsIoo.2
              (show 0 < Real.pi / 2 by positivity)
          simpa [Romik.angle] using hm
      exact Romik.not_mem_innerQuadrantAt_of_mem_sofa p hq hangleIoo

/-- The inverse frame at time zero places the concrete sofa in the horizontal
arm. -/
theorem Romik.initial_arm_of_path_zero
    (p : Romik.Params) (hzero : Romik.path p 0 = (0, 0)) :
    ((Romik.frame p 0).inv.act '' Romik.sofa p) ⊆ horizontalArm := by
  rintro y ⟨q, hq, rfl⟩
  have htime : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
    constructor <;> positivity
  have hs := hq.1.2 0 htime
  have hx : q.1 ≤ 1 := by
    have hu := hs.1
    simpa [supportHalfU, dot, u, hzero] using hu
  have hy0 : 0 ≤ q.2 := hq.1.1
  have hy1 : q.2 ≤ 1 := by
    have hv := hs.2
    simpa [supportHalfV, dot, v, hzero] using hv
  rw [Romik.frame_inv_act_formula]
  simpa [Romik.angle, hzero, dot, u, v, horizontalArm] using
    (show q.1 ≤ 1 ∧ 0 ≤ q.2 ∧ q.2 ≤ 1 from ⟨hx, hy0, hy1⟩)

/-- The inverse frame at time one places the concrete sofa in the vertical
arm. -/
theorem Romik.final_arm_of_path_end_y_zero
    (p : Romik.Params)
    (hend : (Romik.path p (Real.pi / 2)).2 = 0) :
    ((Romik.frame p 1).inv.act '' Romik.sofa p) ⊆ verticalArm := by
  rintro y ⟨q, hq, rfl⟩
  have htime : Real.pi / 2 ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
    constructor
    · positivity
    · rfl
  have hs := hq.1.2 (Real.pi / 2) htime
  have hy0 : 0 ≤ q.2 := hq.1.1
  have hy1 : q.2 ≤ 1 := by
    have hu := hs.1
    simpa [supportHalfU, dot, u, hend] using hu
  have hv := hs.2
  have hv1 :
      dot (q.1 - (Romik.path p (Real.pi / 2)).1,
           q.2 - (Romik.path p (Real.pi / 2)).2) (v (Real.pi / 2)) ≤ 1 := by
    change dot q (v (Real.pi / 2)) ≤
      dot (Romik.path p (Real.pi / 2)) (v (Real.pi / 2)) + 1 at hv
    dsimp [dot] at hv ⊢
    linarith
  rw [Romik.frame_inv_act_formula]
  simpa [Romik.angle, dot, u, v, hend, verticalArm] using
    (show 0 ≤ q.2 ∧ q.2 ≤ 1 ∧
      dot (q.1 - (Romik.path p (Real.pi / 2)).1,
           q.2 - (Romik.path p (Real.pi / 2)).2) (v (Real.pi / 2)) ≤ 1
      from ⟨hy0, hy1, hv1⟩)

end GerverSofa
