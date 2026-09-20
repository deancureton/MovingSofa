import GerverSofa.Boxes
import GerverSofa.Geometry

/-!
# Identification with Romik's hallway-intersection reconstruction

This is the set-theoretic part of Proposition `prop:gerver`.  It uses only the
literal definitions and the two endpoint normalisations; the eighteen-piece
boundary statement remains a separate field of `FullArticleCertificate`.
-/

noncomputable section

namespace GerverSofa.Romik


/-- Romik's fixed-frame reconstruction: initial arm, every supporting hallway,
and the final transported vertical arm. -/
def reconstructedSet (p : Params) : Set Point :=
  {q | q ∈ horizontalArm ∧
    (∀ s ∈ Set.Icc (0 : ℝ) 1, q ∈ hallwayAt p s) ∧
    q ∈ (frame p 1).act '' verticalArm}

/-- Convert a physical angle in `[0,π/2]` to normalized time. -/
def normalizedTime (t : ℝ) : ℝ := t / (Real.pi / 2)

@[simp] theorem angle_normalizedTime (t : ℝ) :
    angle (normalizedTime t) = t := by
  have hT : Real.pi / 2 ≠ 0 := by positivity
  simp [angle, normalizedTime, hT]

 theorem normalizedTime_mem_unit {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    normalizedTime t ∈ Set.Icc (0 : ℝ) 1 := by
  have hT : 0 < Real.pi / 2 := by positivity
  constructor
  · exact div_nonneg ht.1 (le_of_lt hT)
  · exact (div_le_iff₀ hT).2 (by simpa using ht.2)

/-- Every point of the cap-minus-niche set lies in Romik's hallway
intersection reconstruction. -/
theorem sofa_subset_reconstructedSet
    (p : Params)
    (hzero : path p 0 = (0, 0))
    (hend : (path p (Real.pi / 2)).2 = 0) :
    sofa p ⊆ reconstructedSet p := by
  intro q hq
  refine ⟨?_, ?_, ?_⟩
  · have hi : (frame p 0).inv.act q ∈ horizontalArm :=
      initial_arm_of_path_zero p hzero ⟨q, hq, rfl⟩
    simpa [frame, angle, hzero, SE2.inv, SE2.act] using hi
  · intro s hs
    exact sofa_subset_hallwayAt p hzero hend s hs hq
  · have hf : (frame p 1).inv.act q ∈ verticalArm :=
      final_arm_of_path_end_y_zero p hend ⟨q, hq, rfl⟩
    exact ⟨(frame p 1).inv.act q, hf, (frame p 1).act_inv_act q⟩

/-- Membership in every physical supporting hallway gives all outer support
inequalities in the cap definition. -/
theorem mem_K0_of_mem_all_hallways
    (p : Params) {q : Point}
    (hbase : 0 ≤ q.2)
    (hall : ∀ s ∈ Set.Icc (0 : ℝ) 1, q ∈ hallwayAt p s) :
    q ∈ K0 p := by
  refine ⟨hbase, ?_⟩
  intro t ht
  let s := normalizedTime t
  have hs : s ∈ Set.Icc (0 : ℝ) 1 := normalizedTime_mem_unit ht
  have hhall := hall s hs
  have hwall :
      (dot (q.1 - (path p t).1, q.2 - (path p t).2) (u t) ≤ 1 ∧
       dot (q.1 - (path p t).1, q.2 - (path p t).2) (v t) ≤ 1) ∧
      ¬ (dot (q.1 - (path p t).1, q.2 - (path p t).2) (u t) < 0 ∧
         dot (q.1 - (path p t).1, q.2 - (path p t).2) (v t) < 0) := by
    rw [mem_hallwayAt_iff_wall_coordinates] at hhall
    simpa [s] using hhall
  constructor
  · change dot q (u t) ≤ dot (path p t) (u t) + 1
    dsimp [dot] at hwall ⊢
    linarith [hwall.1.1]
  · change dot q (v t) ≤ dot (path p t) (v t) + 1
    dsimp [dot] at hwall ⊢
    linarith [hwall.1.2]

/-- Membership in every physical hallway excludes every open interior-time
inner quadrant. -/
theorem not_mem_innerUnion_of_mem_all_hallways
    (p : Params) {q : Point}
    (hall : ∀ s ∈ Set.Icc (0 : ℝ) 1, q ∈ hallwayAt p s) :
    q ∉ innerUnion p := by
  rintro ⟨t, ht, hinner⟩
  let s := normalizedTime t
  have htIcc : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
    ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have hs : s ∈ Set.Icc (0 : ℝ) 1 := normalizedTime_mem_unit htIcc
  have hhall := hall s hs
  rw [mem_hallwayAt_iff_wall_coordinates] at hhall
  have hwall :
      ¬ (dot (q.1 - (path p t).1, q.2 - (path p t).2) (u t) < 0 ∧
         dot (q.1 - (path p t).1, q.2 - (path p t).2) (v t) < 0) := by
    simpa [s] using hhall.2
  exact hwall (by simpa [innerQuadrantAt] using hinner)

/-- Conversely, Romik's hallway intersection lies in the concrete
cap-minus-niche set. -/
theorem reconstructedSet_subset_sofa (p : Params) :
    reconstructedSet p ⊆ sofa p := by
  intro q hq
  have hbase : 0 ≤ q.2 := hq.1.2.1
  have hK : q ∈ K0 p := mem_K0_of_mem_all_hallways p hbase hq.2.1
  have hU : q ∉ innerUnion p :=
    not_mem_innerUnion_of_mem_all_hallways p hq.2.1
  refine ⟨hK, ?_⟩
  rintro ⟨_hfan, hinner⟩
  exact hU hinner

/-- Set-theoretic identification `G = Sₓ`, conditional only on the endpoint
normalisations already isolated by the main certificate. -/
theorem sofa_eq_reconstructedSet
    (p : Params)
    (hzero : path p 0 = (0, 0))
    (hend : (path p (Real.pi / 2)).2 = 0) :
    sofa p = reconstructedSet p := by
  apply Set.Subset.antisymm
  · exact sofa_subset_reconstructedSet p hzero hend
  · exact reconstructedSet_subset_sofa p

end GerverSofa.Romik
