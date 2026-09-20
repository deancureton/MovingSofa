import GerverSofa.KernelOnly.PartB.Parameters

/-!
# Core semantic infrastructure for the Part B cell certificate

Hull, time-cell, certified-root-coordinate and trigonometric containment lemmas
are isolated here so the five analytic phases can be compiled and diagnosed
independently.
-/

noncomputable section

namespace GerverSofa
namespace PartB

open RatInterval

/-! ## Hull and time-cell semantics -/

theorem contains_intervalHull_left {a b : RatInterval} {x : ℝ}
    (hx : Contains a x) : Contains (intervalHull a b) x := by
  constructor
  · have hmin : min a.lo b.lo ≤ a.lo := min_le_left _ _
    exact le_trans (by exact_mod_cast hmin) hx.1
  · have hmax : a.hi ≤ max a.hi b.hi := le_max_left _ _
    exact le_trans hx.2 (by exact_mod_cast hmax)

theorem contains_intervalHull_right {a b : RatInterval} {x : ℝ}
    (hx : Contains b x) : Contains (intervalHull a b) x := by
  constructor
  · have hmin : min a.lo b.lo ≤ b.lo := min_le_right _ _
    exact le_trans (by exact_mod_cast hmin) hx.1
  · have hmax : b.hi ≤ max a.hi b.hi := le_max_right _ _
    exact le_trans hx.2 (by exact_mod_cast hmax)

theorem pointContains_hull_left {a b : RatInterval × RatInterval} {x : Point}
    (hx : PointContains a x) : PointContains (pointHull a b) x := by
  exact ⟨contains_intervalHull_left hx.1,
    contains_intervalHull_left hx.2⟩

theorem pointContains_hull_right {a b : RatInterval × RatInterval} {x : Point}
    (hx : PointContains b x) : PointContains (pointHull a b) x := by
  exact ⟨contains_intervalHull_right hx.1,
    contains_intervalHull_right hx.2⟩

theorem nodeTime_mono {i j : Nat} (hij : i ≤ j) :
    nodeTime i ≤ nodeTime j := by
  unfold nodeTime nodeCoeff
  apply mul_le_mul_of_nonneg_right _ Real.pi_pos.le
  norm_num
  have hijR : (i : ℝ) ≤ (j : ℝ) := by
    exact_mod_cast hij
  exact div_le_div_of_nonneg_right hijR (by norm_num)

theorem cellTimeInterval_contains_start (i : Cell) :
    Contains (cellTimeInterval i) (nodeTime i.1) := by
  apply contains_intervalHull_left
  simpa [nodeTime, nodeCoeff, ExactReplay.scale] using
    (RatInterval.contains_scale (a := nodeCoeff i.1)
      ExactReplay.piI_contains_pi)

theorem cellTimeInterval_contains_end (i : Cell) :
    Contains (cellTimeInterval i) (nodeTime (i.1 + 1)) := by
  apply contains_intervalHull_right
  simpa [nodeTime, nodeCoeff, ExactReplay.scale] using
    (RatInterval.contains_scale (a := nodeCoeff (i.1 + 1))
      ExactReplay.piI_contains_pi)

theorem cellTimeInterval_contains {i : Cell} {t : ℝ}
    (ht : t ∈ cellSet i) : Contains (cellTimeInterval i) t := by
  exact ⟨le_trans (cellTimeInterval_contains_start i).1 ht.1,
    le_trans ht.2 (cellTimeInterval_contains_end i).2⟩

/-! ## The Part A root is enclosed coordinatewise -/

theorem root_coord_contains (k : Fin 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox k.1)
      (PartALeanCert.fullRoot k) := by
  exact ((Romik.inputBox_exact PartALeanCert.fullRoot).1
    PartALeanCert.fullRoot_mem).2 k

theorem k11_contains :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 0) params.k11 := by
  change Contains (ExactReplay.getI ExactReplay.fullInputBox 0)
    (PartALeanCert.fullRoot (0 : Fin 22))
  exact root_coord_contains (0 : Fin 22)
theorem k12_contains :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 1) params.k12 := by
  change Contains (ExactReplay.getI ExactReplay.fullInputBox 1)
    (PartALeanCert.fullRoot (1 : Fin 22))
  exact root_coord_contains (1 : Fin 22)
theorem k21_contains :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 2) params.k21 := by
  change Contains (ExactReplay.getI ExactReplay.fullInputBox 2)
    (PartALeanCert.fullRoot (2 : Fin 22))
  exact root_coord_contains (2 : Fin 22)
theorem k22_contains :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 3) params.k22 := by
  change Contains (ExactReplay.getI ExactReplay.fullInputBox 3)
    (PartALeanCert.fullRoot (3 : Fin 22))
  exact root_coord_contains (3 : Fin 22)
theorem k31_contains :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 4) params.k31 := by
  change Contains (ExactReplay.getI ExactReplay.fullInputBox 4)
    (PartALeanCert.fullRoot (4 : Fin 22))
  exact root_coord_contains (4 : Fin 22)
theorem k32_contains :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 5) params.k32 := by
  change Contains (ExactReplay.getI ExactReplay.fullInputBox 5)
    (PartALeanCert.fullRoot (5 : Fin 22))
  exact root_coord_contains (5 : Fin 22)
theorem k41_contains :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 6) params.k41 := by
  change Contains (ExactReplay.getI ExactReplay.fullInputBox 6)
    (PartALeanCert.fullRoot (6 : Fin 22))
  exact root_coord_contains (6 : Fin 22)
theorem k42_contains :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 7) params.k42 := by
  change Contains (ExactReplay.getI ExactReplay.fullInputBox 7)
    (PartALeanCert.fullRoot (7 : Fin 22))
  exact root_coord_contains (7 : Fin 22)
theorem k51_contains :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 8) params.k51 := by
  change Contains (ExactReplay.getI ExactReplay.fullInputBox 8)
    (PartALeanCert.fullRoot (8 : Fin 22))
  exact root_coord_contains (8 : Fin 22)
theorem k52_contains :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 9) params.k52 := by
  change Contains (ExactReplay.getI ExactReplay.fullInputBox 9)
    (PartALeanCert.fullRoot (9 : Fin 22))
  exact root_coord_contains (9 : Fin 22)
theorem a1_contains :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 10) params.a1 := by
  change Contains (ExactReplay.getI ExactReplay.fullInputBox 10)
    (PartALeanCert.fullRoot (10 : Fin 22))
  exact root_coord_contains (10 : Fin 22)
theorem a2_contains :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 11) params.a2 := by
  change Contains (ExactReplay.getI ExactReplay.fullInputBox 11)
    (PartALeanCert.fullRoot (11 : Fin 22))
  exact root_coord_contains (11 : Fin 22)
theorem b1_contains :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 12) params.b1 := by
  change Contains (ExactReplay.getI ExactReplay.fullInputBox 12)
    (PartALeanCert.fullRoot (12 : Fin 22))
  exact root_coord_contains (12 : Fin 22)
theorem b2_contains :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 13) params.b2 := by
  change Contains (ExactReplay.getI ExactReplay.fullInputBox 13)
    (PartALeanCert.fullRoot (13 : Fin 22))
  exact root_coord_contains (13 : Fin 22)
theorem c1_contains :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 14) params.c1 := by
  change Contains (ExactReplay.getI ExactReplay.fullInputBox 14)
    (PartALeanCert.fullRoot (14 : Fin 22))
  exact root_coord_contains (14 : Fin 22)
theorem c2_contains :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 15) params.c2 := by
  change Contains (ExactReplay.getI ExactReplay.fullInputBox 15)
    (PartALeanCert.fullRoot (15 : Fin 22))
  exact root_coord_contains (15 : Fin 22)
theorem d1_contains :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 16) params.d1 := by
  change Contains (ExactReplay.getI ExactReplay.fullInputBox 16)
    (PartALeanCert.fullRoot (16 : Fin 22))
  exact root_coord_contains (16 : Fin 22)
theorem d2_contains :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 17) params.d2 := by
  change Contains (ExactReplay.getI ExactReplay.fullInputBox 17)
    (PartALeanCert.fullRoot (17 : Fin 22))
  exact root_coord_contains (17 : Fin 22)
theorem e1_contains :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 18) params.e1 := by
  change Contains (ExactReplay.getI ExactReplay.fullInputBox 18)
    (PartALeanCert.fullRoot (18 : Fin 22))
  exact root_coord_contains (18 : Fin 22)
theorem e2_contains :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 19) params.e2 := by
  change Contains (ExactReplay.getI ExactReplay.fullInputBox 19)
    (PartALeanCert.fullRoot (19 : Fin 22))
  exact root_coord_contains (19 : Fin 22)

theorem point_contains (q : ℚ) : Contains (RatInterval.point q) (q : ℝ) :=
  (RatInterval.contains_point_iff q (q : ℝ)).2 rfl

theorem trig_contains {i : Cell} {t : ℝ}
    (htCell : t ∈ cellSet i) (htPhys : t ∈ physicalInterval) :
    Contains (ExactReplay.cosineInterval (cellTimeInterval i)) (Real.cos t) ∧
    Contains (ExactReplay.sineInterval (cellTimeInterval i)) (Real.sin t) := by
  have htI := cellTimeInterval_contains htCell
  exact ⟨ExactReplay.cosI_contains htI htPhys.1 htPhys.2,
    ExactReplay.sinI_contains htI htPhys.1 htPhys.2⟩

end PartB
end GerverSofa
