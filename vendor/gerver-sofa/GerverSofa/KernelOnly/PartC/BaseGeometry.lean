import GerverSofa.KernelOnly.PartC.GlobalSupport

/-!
# Part C geometric consequences already closed by the existing source

Closedness, supporting-hallway containment, endpoint arms, motion continuity
and the set-theoretic identification with Romik's reconstruction require no new
numerical replay.  They are collected here for the concrete certified
parameter vector.
-/

noncomputable section

namespace GerverSofa
namespace PartC

 theorem closed_G : IsClosed G := Romik.isClosed_sofa params

 theorem G_subset_hallway :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, G ⊆ Romik.hallwayAt params s :=
  Romik.sofa_subset_hallwayAt params pathZero pathEndYZero

 theorem initialArm : ((frame 0).inv.act '' G) ⊆ horizontalArm :=
  Romik.initial_arm_of_path_zero params pathZero

 theorem finalArm : ((frame 1).inv.act '' G) ⊆ verticalArm :=
  Romik.final_arm_of_path_end_y_zero params pathEndYZero

 theorem G_eq_Sx : G = Sx :=
  Romik.sofa_eq_reconstructedSet params pathZero pathEndYZero

end PartC
end GerverSofa
