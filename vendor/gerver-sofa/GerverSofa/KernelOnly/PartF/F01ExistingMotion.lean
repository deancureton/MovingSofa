import GerverSofa.KernelOnly.PartC.Stage4.FinalTopologyClosure

/-!
# F01: exact identity normalization of the already certified motion

The original project asks for an initial translation. For its concrete
Gerver path the inverse frame is exactly the identity, which is the
stronger normalization required by DeepMind. These statements refer to
the existing `ℝ × ℝ` coordinate model, not to an unproved isometry between
the product norm and the Euclidean norm.
-/

noncomputable section

namespace GerverSofa.PartF.Existing

def motion (s : ℝ) : SE2 := (PartC.frame s).inv

theorem motion_zero : motion 0 = SE2.one := by
  change (Romik.frame PartC.params 0).inv = SE2.one
  simp [Romik.frame, Romik.angle, PartC.pathZero, SE2.inv, SE2.one]

theorem motion_continuous : SE2.ContinuousPath motion :=
  SE2.continuousPath_inv PartC.frameContinuous

theorem initial : PartC.G ⊆ horizontalArm := by
  intro q hq
  have h := PartC.initialArm ⟨q, hq, rfl⟩
  change (motion 0).act q ∈ horizontalArm at h
  rw [motion_zero, SE2.one_act] at h
  exact h

theorem all_times :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, (motion s).act '' PartC.G ⊆ hallway := by
  intro s hs
  exact inv_image_subset_hallway_of_subset_supporting
    (PartC.frame s) PartC.G (PartC.G_subset_hallway s hs)

theorem final : (motion 1).act '' PartC.G ⊆ verticalArm := PartC.finalArm

end GerverSofa.PartF.Existing
