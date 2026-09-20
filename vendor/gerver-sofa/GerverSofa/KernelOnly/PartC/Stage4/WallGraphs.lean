import GerverSofa.KernelOnly.PartC.Stage4.ExactGeometryFacts

/-!
# Part C Stage 4: inner-wall graph identities
-/

noncomputable section

namespace GerverSofa
namespace PartC
namespace Stage4

open Set

/-- First inner wall as a graph over horizontal coordinate. -/
def bRoof (t X : ℝ) : ℝ :=
  (dot (Romik.path params t) (u t) - X * Real.cos t) / Real.sin t

/-- Second inner wall as a graph over horizontal coordinate. -/
def dRoof (t X : ℝ) : ℝ :=
  (dot (Romik.path params t) (v t) + X * Real.sin t) / Real.cos t

/-- Vertical roof of one instantaneous open inner quadrant. -/
def instantRoof (t X : ℝ) : ℝ := min (bRoof t X) (dRoof t X)

/-- A point of nonnegative height is in the instantaneous inner quadrant iff it
lies strictly below both graph roofs. -/
theorem mem_innerQuadrant_iff_roofs {t X Y : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    (X,Y) ∈ Romik.innerQuadrantAt params t ↔
      Y < bRoof t X ∧ Y < dRoof t X := by
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1 (lt_trans ht.2 (by
    dsimp [T]; linarith [Real.pi_pos]))
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ⟨by
    linarith [Real.pi_pos, ht.1], by simpa [T] using ht.2⟩
  simp [Romik.innerQuadrantAt, bRoof, dRoof, dot, u, v]
  constructor
  · rintro ⟨hu,hv⟩
    constructor
    · apply (lt_div_iff₀ hs).2
      linarith
    · apply (lt_div_iff₀ hc).2
      linarith
  · rintro ⟨hb,hd⟩
    constructor
    · have := (lt_div_iff₀ hs).1 hb
      linarith
    · have := (lt_div_iff₀ hc).1 hd
      linarith

/-- The two walls agree at their apex. -/
theorem roofs_at_path (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    bRoof t (Romik.path params t).1 = (Romik.path params t).2 ∧
    dRoof t (Romik.path params t).1 = (Romik.path params t).2 := by
  have hs : Real.sin t ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi ht.1 (lt_trans ht.2 (by
    dsimp [T]; linarith [Real.pi_pos])))
  have hc : Real.cos t ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by
    linarith [Real.pi_pos, ht.1], by simpa [T] using ht.2⟩)
  constructor <;> simp [bRoof, dRoof, dot, u, v, hs, hc] <;> field_simp <;> ring

end Stage4
end PartC
end GerverSofa
