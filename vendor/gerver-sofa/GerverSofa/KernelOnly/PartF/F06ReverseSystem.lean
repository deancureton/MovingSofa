import GerverSofa.KernelOnly.PartF.F05DictionaryEquations
import GerverSofa.KernelOnly.EndpointSymmetry

/-!
# F06: reverse reduction from the full Romik equations

This direction uses velocity matching and the two contact equations. It does
not assume membership in either numerical box or any strict angle inequality.
-/

noncomputable section
set_option maxHeartbeats 2000000

namespace GerverSofa.PartF.Phases

theorem rot_injective (t : ℝ) : Function.Injective (Romik.rot t) := by
  intro z w h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  dsimp [Romik.rot] at hx hy
  apply Prod.ext
  · linear_combination Real.cos t * hx + Real.sin t * hy -
      (z.1 - w.1) * Real.sin_sq_add_cos_sq t
  · linear_combination -Real.sin t * hx + Real.cos t * hy -
      (z.2 - w.2) * Real.sin_sq_add_cos_sq t

theorem alphaBeta12_eq {p : Romik.Params} (hp : Romik.Equations p) :
    Romik.alphaBeta1 p p.phi = Romik.alphaBeta2 p p.phi := by
  apply rot_injective p.phi
  apply Prod.ext
  · have h := congrFun hp (10 : Fin 22)
    change (Romik.rot p.phi (Romik.alphaBeta1 p p.phi)).1 -
      (Romik.rot p.phi (Romik.alphaBeta2 p p.phi)).1 = 0 at h
    exact sub_eq_zero.mp h
  · have h := congrFun hp (11 : Fin 22)
    change (Romik.rot p.phi (Romik.alphaBeta1 p p.phi)).2 -
      (Romik.rot p.phi (Romik.alphaBeta2 p p.phi)).2 = 0 at h
    exact sub_eq_zero.mp h

theorem alphaBeta23_eq {p : Romik.Params} (hp : Romik.Equations p) :
    Romik.alphaBeta2 p p.theta = Romik.alphaBeta3 p p.theta := by
  apply rot_injective p.theta
  apply Prod.ext
  · have h := congrFun hp (14 : Fin 22)
    change (Romik.rot p.theta (Romik.alphaBeta2 p p.theta)).1 -
      (Romik.rot p.theta (Romik.alphaBeta3 p p.theta)).1 = 0 at h
    exact sub_eq_zero.mp h
  · have h := congrFun hp (15 : Fin 22)
    change (Romik.rot p.theta (Romik.alphaBeta2 p p.theta)).2 -
      (Romik.rot p.theta (Romik.alphaBeta3 p p.theta)).2 = 0 at h
    exact sub_eq_zero.mp h

theorem c2_eq_of_full {p : Romik.Params} (hp : Romik.Equations p) :
    p.c2 = -2 - 2 * p.b1 := by
  have h := congrArg Prod.fst (alphaBeta23_eq hp)
  dsimp [Romik.alphaBeta2, Romik.alphaBeta3] at h
  linarith only [h]

theorem c1_eq_of_full {p : Romik.Params} (hp : Romik.Equations p) :
    p.c1 = Real.pi / 2 - 2 - 2 * p.b1 := by
  have hs := Romik.c2_eq_c1_sub_halfPi_of_equations hp
  have hc := c2_eq_of_full hp
  linarith only [hs, hc]

theorem reverse_equation4 {p : Romik.Params} (hp : Romik.Equations p) :
    Reduced.system (undictionary p) 3 = 0 := by
  have h := congrArg Prod.snd (alphaBeta23_eq hp)
  dsimp [Romik.alphaBeta2, Romik.alphaBeta3] at h
  rw [c1_eq_of_full hp] at h
  change (undictionary p).a + Real.pi / 2 - (undictionary p).phi -
    (undictionary p).theta - (undictionary p).b +
    1 / 2 * ((undictionary p).theta - (undictionary p).phi) *
      (1 + (undictionary p).a) +
    1 / 4 * ((undictionary p).theta - (undictionary p).phi) *
      ((undictionary p).theta - (undictionary p).phi) = 0
  dsimp [undictionary]
  linear_combination -h

theorem reverse_equation3 {p : Romik.Params} (hp : Romik.Equations p) :
    Reduced.system (undictionary p) 2 = 0 := by
  have ha := congrArg Prod.fst (alphaBeta12_eq hp)
  have hb := congrArg Prod.snd (alphaBeta12_eq hp)
  dsimp [Romik.alphaBeta1, Romik.alphaBeta2] at ha hb
  rw [Romik.a2_eq_neg_quarter_of_equations hp] at ha hb
  change (undictionary p).a * Real.cos (undictionary p).phi -
    Real.sin (undictionary p).phi - 1 / 2 +
    1 / 2 * Real.cos (undictionary p).phi -
    (undictionary p).b * Real.sin (undictionary p).phi = 0
  dsimp [undictionary]
  linear_combination Real.cos p.phi * ha + Real.sin p.phi * hb +
    (1 / 2 : ℝ) * Real.sin_sq_add_cos_sq p.phi

theorem reverse_equation1 {p : Romik.Params} (hp : Romik.Equations p) :
    Reduced.system (undictionary p) 0 = 0 := by
  have h9 := congrFun hp (9 : Fin 22)
  have h13 := congrFun hp (13 : Fin 22)
  have h21 := congrFun hp (21 : Fin 22)
  change (Romik.path1 p p.phi).2 - (Romik.path2 p p.phi).2 = 0 at h9
  change (Romik.path2 p p.theta).2 - (Romik.path3 p p.theta).2 = 0 at h13
  change (Romik.path1 p p.phi).2 -
    ((Romik.path3 p (Real.pi / 2 - p.theta)).2 +
      (Romik.alphaBeta3 p (Real.pi / 2 - p.theta)).1 *
        Real.cos (Real.pi / 2 - p.theta)) = 0 at h21
  dsimp [Romik.path1, Romik.path2, Romik.path3, Romik.rot, Romik.addK,
    Romik.alphaBeta3] at h9 h13 h21
  simp only [c1_eq_of_full hp, c2_eq_of_full hp] at h13 h21
  simp only [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub] at h21
  have h4 := reverse_equation4 hp
  change (undictionary p).a + Real.pi / 2 - (undictionary p).phi -
    (undictionary p).theta - (undictionary p).b +
    1 / 2 * ((undictionary p).theta - (undictionary p).phi) *
      (1 + (undictionary p).a) +
    1 / 4 * ((undictionary p).theta - (undictionary p).phi) *
      ((undictionary p).theta - (undictionary p).phi) = 0 at h4
  change (undictionary p).a * (Real.cos (undictionary p).theta -
    Real.cos (undictionary p).phi) - 2 * (undictionary p).b *
    Real.sin (undictionary p).phi +
    ((undictionary p).theta - (undictionary p).phi - 1) *
    Real.cos (undictionary p).theta - Real.sin (undictionary p).theta +
    Real.cos (undictionary p).phi + Real.sin (undictionary p).phi = 0
  dsimp [undictionary] at h4 ⊢
  linear_combination -2 * h21 + 2 * h9 + 2 * h13 + 2 * Real.sin p.theta * h4

theorem reverse_equation2 {p : Romik.Params} (hp : Romik.Equations p) :
    Reduced.system (undictionary p) 1 = 0 := by
  have h8 := congrFun hp (8 : Fin 22)
  have h12 := congrFun hp (12 : Fin 22)
  have h20 := congrFun hp (20 : Fin 22)
  change (Romik.path1 p p.phi).1 - (Romik.path2 p p.phi).1 = 0 at h8
  change (Romik.path2 p p.theta).1 - (Romik.path3 p p.theta).1 = 0 at h12
  change (Romik.path1 p p.phi).1 -
    ((Romik.path3 p (Real.pi / 2 - p.theta)).1 -
      (Romik.alphaBeta3 p (Real.pi / 2 - p.theta)).1 *
        Real.sin (Real.pi / 2 - p.theta)) = 0 at h20
  dsimp [Romik.path1, Romik.path2, Romik.path3, Romik.rot, Romik.addK,
    Romik.alphaBeta3] at h8 h12 h20
  simp only [c1_eq_of_full hp, c2_eq_of_full hp] at h12 h20
  simp only [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub] at h20
  have h4 := reverse_equation4 hp
  change (undictionary p).a + Real.pi / 2 - (undictionary p).phi -
    (undictionary p).theta - (undictionary p).b +
    1 / 2 * ((undictionary p).theta - (undictionary p).phi) *
      (1 + (undictionary p).a) +
    1 / 4 * ((undictionary p).theta - (undictionary p).phi) *
      ((undictionary p).theta - (undictionary p).phi) = 0 at h4
  change (undictionary p).a * (3 * Real.sin (undictionary p).theta +
    Real.sin (undictionary p).phi) - 2 * (undictionary p).b *
    Real.cos (undictionary p).phi +
    3 * ((undictionary p).theta - (undictionary p).phi - 1) *
    Real.sin (undictionary p).theta + 3 * Real.cos (undictionary p).theta -
    Real.sin (undictionary p).phi + Real.cos (undictionary p).phi = 0
  dsimp [undictionary] at h4 ⊢
  linear_combination -2 * h20 + 2 * h8 + 2 * h12 + 2 * Real.cos p.theta * h4

theorem undictionary_equations {p : Romik.Params} (hp : Romik.Equations p) :
    Reduced.Equations (undictionary p) := by
  change Reduced.system (undictionary p) = 0
  funext i
  fin_cases i
  · exact reverse_equation1 hp
  · exact reverse_equation2 hp
  · exact reverse_equation3 hp
  · exact reverse_equation4 hp

end GerverSofa.PartF.Phases
