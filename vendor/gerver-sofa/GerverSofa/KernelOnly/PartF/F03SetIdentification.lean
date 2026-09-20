import GerverSofa.KernelOnly.PartF.F03CanonicalRotation

/-!
# F03: the certified set as a canonical hallway intersection

We transport the existing reconstruction theorem, including the endpoint arms,
to the Euclidean world-frame convention. The final conditional interfaces state
the outstanding path/dictionary equalities explicitly. They do not prove the
literal integral representation or identify the certified 22D tuple.
-/

noncomputable section
open scoped unitInterval
set_option maxHeartbeats 800000

namespace GerverSofa.PartF.SetIdentification

open Coordinates EuclideanMotion CanonicalRotation

theorem mem_coordinate_image (S : Set Point) (q : Plane) :
    q ∈ toPlane '' S ↔ fromPlane q ∈ S := by
  rw [image_eq_preimage]
  rfl

theorem mem_ofSE2_image (g : SE2) (S : Set Point) (q : Plane) :
    q ∈ ofSE2 g '' (toPlane '' S) ↔ fromPlane q ∈ g.act '' S := by
  rw [image_action, mem_coordinate_image]

/-- The change from real unit time to subtype unit time loses no constraint. -/
theorem reconstructedSet_image (p : Romik.Params)
    (hzero : Romik.path p 0 = (0, 0)) :
    toPlane '' Romik.reconstructedSet p =
      frameIntersection (fun s : I => ofSE2 (Romik.frame p (s : ℝ)))
        Model.horizontalHallway Model.verticalHallway Model.hallway := by
  have hstart : (Romik.frame p 0).act '' horizontalArm = horizontalArm := by
    have hfun : (Romik.frame p 0).act = id :=
      funext (romikFrame_zero_act p hzero)
    rw [hfun, Set.image_id]
  ext q
  simp only [frameIntersection, ← horizontal_image, ← vertical_image,
    ← hallway_image, Set.mem_inter_iff, Set.mem_iInter,
    mem_ofSE2_image, mem_coordinate_image]
  change (fromPlane q ∈ horizontalArm ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1,
        fromPlane q ∈ (Romik.frame p s).act '' hallway) ∧
      fromPlane q ∈ (Romik.frame p 1).act '' verticalArm) ↔
    (fromPlane q ∈ (Romik.frame p 0).act '' horizontalArm ∧
      fromPlane q ∈ (Romik.frame p 1).act '' verticalArm) ∧
      ∀ s : I, fromPlane q ∈ (Romik.frame p (s : ℝ)).act '' hallway
  rw [hstart]
  constructor
  · rintro ⟨hi, hall, hf⟩
    exact ⟨⟨hi, hf⟩, fun s => hall (s : ℝ) s.property⟩
  · rintro ⟨⟨hi, hf⟩, hall⟩
    exact ⟨hi, fun s hs => hall ⟨s, hs⟩, hf⟩

theorem reconstructedSet_image_eq_worldSofa (p : Romik.Params)
    (hzero : Romik.path p 0 = (0, 0)) :
    toPlane '' Romik.reconstructedSet p =
      worldSofa (fun t => toPlane (Romik.path p t))
        Model.horizontalHallway Model.verticalHallway Model.hallway := by
  rw [reconstructedSet_image p hzero, worldSofa, angleIntersection_eq_frameIntersection]
  have hframes :
      (fun s : I => ofSE2 (Romik.frame p (s : ℝ))) =
      (fun s : I => worldFrame ((s : ℝ) * (Real.pi / 2))
        (toPlane (Romik.path p ((s : ℝ) * (Real.pi / 2))))) := by
    funext s
    exact romikFrame_eq_worldFrame p (s : ℝ)
  exact congrArg (fun F => frameIntersection F
    Model.horizontalHallway Model.verticalHallway Model.hallway) hframes

/-- An unconditional identification of the concrete, already certified set. -/
theorem sofa_eq_worldSofa :
    EuclideanMotion.sofa =
      worldSofa (fun t => toPlane (Romik.path PartC.params t))
        Model.horizontalHallway Model.verticalHallway Model.hallway := by
  change toPlane '' PartC.G = _
  rw [PartC.G_eq_Sx]
  exact reconstructedSet_image_eq_worldSofa PartC.params PartC.pathZero

end GerverSofa.PartF.SetIdentification
