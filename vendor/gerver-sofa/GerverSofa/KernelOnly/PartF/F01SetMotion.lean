import GerverSofa.KernelOnly.PartF.F01AffineOrder

/-!
# F01: supporting intersections and their continuous inverse motion

`Model.IsMovingSofa` has the seven fields and the rigid-motion topology of
the upstream definition. This local, independently named model avoids
importing upstream conjectures with unfinished proof terms. Its concrete
instantiation for the integral Gerver path still needs the analytic bridge.
-/

noncomputable section
open scoped unitInterval

namespace GerverSofa.PartF

def frameIntersection (F : I → Rigid) (H V L : Set Plane) : Set Plane :=
  F 0 '' H ∩ F 1 '' V ∩ ⋂ s, F s '' L

def angleIntersection (F : ℝ → Rigid) (H V L : Set Plane) : Set Plane :=
  F 0 '' H ∩ F (Real.pi / 2) '' V ∩
    ⋂ t ∈ Set.Icc 0 (Real.pi / 2), F t '' L

def bodySofa (p : ℝ → Plane) (H V L : Set Plane) : Set Plane :=
  angleIntersection (fun t => bodyFrame t (p t)) H V L

def worldSofa (x : ℝ → Plane) (H V L : Set Plane) : Set Plane :=
  angleIntersection (fun t => worldFrame t (x t)) H V L

theorem bodySofa_eq_worldSofa_of_path_identity
    (p x : ℝ → Plane) (H V L : Set Plane)
    (hpath : ∀ t ∈ Set.Icc 0 (Real.pi / 2), x t = rotation t (p t)) :
    bodySofa p H V L = worldSofa x H V L := by
  have hT : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have h0 := hpath 0 ⟨le_rfl, hT⟩
  have h1 := hpath (Real.pi / 2) ⟨hT, le_rfl⟩
  -- Expose the applications before rewriting under the image coercions.
  change
    bodyFrame 0 (p 0) '' H ∩
      bodyFrame (Real.pi / 2) (p (Real.pi / 2)) '' V ∩
        (⋂ t ∈ Set.Icc 0 (Real.pi / 2), bodyFrame t (p t) '' L) =
    worldFrame 0 (x 0) '' H ∩
      worldFrame (Real.pi / 2) (x (Real.pi / 2)) '' V ∩
        (⋂ t ∈ Set.Icc 0 (Real.pi / 2), worldFrame t (x t) '' L)
  rw [bodyFrame_eq_worldFrame, ← h0, bodyFrame_eq_worldFrame, ← h1]
  congr 1
  apply Set.iInter_congr
  intro t
  apply Set.iInter_congr
  intro ht
  rw [bodyFrame_eq_worldFrame, ← hpath t ht]

/-- Normalizing the physical angle does not change the intersection. -/
theorem angleIntersection_eq_frameIntersection
    (F : ℝ → Rigid) (H V L : Set Plane) :
    angleIntersection F H V L =
      frameIntersection (fun s : I => F ((s : ℝ) * (Real.pi / 2))) H V L := by
  have hT : (0 : ℝ) < Real.pi / 2 := by positivity
  have hz : ((0 : I) : ℝ) = 0 := rfl
  have ho : ((1 : I) : ℝ) = 1 := rfl
  ext q
  simp only [angleIntersection, frameIntersection, Set.mem_inter_iff,
    Set.mem_iInter, hz, ho, zero_mul, one_mul]
  constructor
  · rintro ⟨hends, hall⟩
    refine ⟨hends, ?_⟩
    intro s
    apply hall
    exact ⟨mul_nonneg s.property.1 hT.le,
      by nlinarith [s.property.2]⟩
  · rintro ⟨hends, hall⟩
    refine ⟨hends, ?_⟩
    intro t ht
    let s : I := ⟨t / (Real.pi / 2), div_nonneg ht.1 hT.le,
      (div_le_iff₀ hT).2 (by simpa using ht.2)⟩
    have h := hall s
    simpa only [s, div_mul_cancel₀ t (ne_of_gt hT)] using h

namespace Model

def horizontalHallway : Set Plane := {q | q 0 ≤ 1 ∧ 0 ≤ q 1 ∧ q 1 ≤ 1}
def verticalHallway : Set Plane := {q | 0 ≤ q 0 ∧ q 0 ≤ 1 ∧ q 1 ≤ 1}
def hallway : Set Plane := horizontalHallway ∪ verticalHallway

structure IsMovingSofa (S : Set Plane) (m : I → Rigid) : Prop where
  isConnected : IsConnected S
  isClosed : IsClosed S
  continuous : Continuous m
  zero : m 0 = AffineIsometryEquiv.refl ℝ Plane
  initial : S ⊆ horizontalHallway
  subset_hallway : ∀ s, m s '' S ⊆ hallway
  final : m 1 '' S ⊆ verticalHallway

end Model

end GerverSofa.PartF
