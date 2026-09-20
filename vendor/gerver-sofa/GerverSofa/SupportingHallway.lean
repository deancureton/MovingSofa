import GerverSofa.SE2

/-!
# Supporting hallway and inverse motion
-/

namespace GerverSofa

/-- World-frame hallway obtained from the standard hallway by `frame`. -/
def supportingHallway (frame : SE2) : Set Point :=
  frame.act '' hallway

/-- Membership in a supporting hallway is equivalent to standard-hallway
membership after applying the inverse frame. -/
theorem mem_supportingHallway_iff (frame : SE2) (q : Point) :
    q ∈ supportingHallway frame ↔ frame.inv.act q ∈ hallway := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    simpa using hp
  · intro hq
    refine ⟨frame.inv.act q, hq, ?_⟩
    exact frame.act_inv_act q

/-- Set-level version of `mem_supportingHallway_iff`. -/
theorem inv_image_subset_hallway_of_subset_supporting
    (frame : SE2) (S : Set Point)
    (hS : S ⊆ supportingHallway frame) :
    frame.inv.act '' S ⊆ hallway := by
  rintro p ⟨q, hqS, rfl⟩
  exact (mem_supportingHallway_iff frame q).1 (hS hqS)

end GerverSofa
