import GerverSofa.KernelOnly.PartC.ContactAlgebra

/-!
# Consequences of the certified Part B continuum margins

The two strict inequalities already certified on the complete square imply
that every point of the Gerver rotation path satisfies every outer supporting
half-plane inequality.  This is one of the main bridges from Part B into the
global geometry of Part C.
-/

noncomputable section

namespace GerverSofa
namespace PartC

 theorem Gu_positive {s t : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) T)
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    0 < PartB.Gu s t := by
  have h := PartB.global_half_plane_margins.1 s (by simpa [T] using hs)
    t (by simpa [T] using ht)
  linarith

 theorem Gv_positive {s t : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) T)
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    0 < PartB.Gv s t := by
  have h := PartB.global_half_plane_margins.2 s (by simpa [T] using hs)
    t (by simpa [T] using ht)
  linarith

/-- Every path point lies in every first outer supporting half-plane. -/
theorem path_mem_supportHalfU {s t : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) T)
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Romik.path params t ∈ supportHalfU params s := by
  have h := Gu_positive hs ht
  change dot (Romik.path params t) (u s) ≤
    dot (Romik.path params s) (u s) + 1
  dsimp [PartB.Gu, dot] at h ⊢
  linarith

/-- Every path point lies in every second outer supporting half-plane. -/
theorem path_mem_supportHalfV {s t : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) T)
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Romik.path params t ∈ supportHalfV params s := by
  have h := Gv_positive hs ht
  change dot (Romik.path params t) (v s) ≤
    dot (Romik.path params s) (v s) + 1
  dsimp [PartB.Gv, dot] at h ⊢
  linarith

 theorem path_mem_outer_supports {s t : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) T)
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Romik.path params t ∈
      supportHalfU params s ∩ supportHalfV params s :=
  ⟨path_mem_supportHalfU hs ht, path_mem_supportHalfV hs ht⟩

end PartC
end GerverSofa
