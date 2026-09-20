import GerverSofa.KernelOnly.PartF.F06ReverseSystem

/-!
# F06: the reverse parameters determine the full solution

Velocity matching determines the shape coefficients. Positional matching
then determines each successive translation. No numerical enclosure is used.
-/

noncomputable section
set_option maxHeartbeats 2000000

namespace GerverSofa.PartF.Phases

theorem full_equations_injective {p q : Romik.Params}
    (hp : Romik.Equations p) (hq : Romik.Equations q)
    (h : undictionary p = undictionary q) : p = q := by
  have hphi : p.phi = q.phi := congrArg Reduced.Params.phi h
  have htheta : p.theta = q.theta := congrArg Reduced.Params.theta h
  have ha := congrArg Reduced.Params.a h
  have hb := congrArg Reduced.Params.b h
  dsimp [undictionary] at ha hb
  have hb1 : p.b1 = q.b1 := by
    rw [hphi] at ha
    linarith only [ha]
  have hb2 : p.b2 = q.b2 := by
    simp only [hphi, hb1] at hb
    linarith only [hb]
  have ha2 : p.a2 = q.a2 := by
    rw [Romik.a2_eq_neg_quarter_of_equations hp,
      Romik.a2_eq_neg_quarter_of_equations hq]
  have ha1 : p.a1 = q.a1 := by
    have hpa := congrArg Prod.fst (alphaBeta12_eq hp)
    have hpb := congrArg Prod.snd (alphaBeta12_eq hp)
    have hqa := congrArg Prod.fst (alphaBeta12_eq hq)
    have hqb := congrArg Prod.snd (alphaBeta12_eq hq)
    dsimp [Romik.alphaBeta1, Romik.alphaBeta2] at hpa hpb hqa hqb
    simp only [hphi, hb1, hb2, ha2] at hpa hpb
    linear_combination (-Real.sin q.phi / 2) * hpa +
      (Real.sin q.phi / 2) * hqa + (Real.cos q.phi / 2) * hpb -
      (Real.cos q.phi / 2) * hqb -
      (p.a1 - q.a1) * Real.sin_sq_add_cos_sq q.phi
  have hc1 : p.c1 = q.c1 := by
    rw [c1_eq_of_full hp, c1_eq_of_full hq, hb1]
  have hc2 : p.c2 = q.c2 := by
    rw [c2_eq_of_full hp, c2_eq_of_full hq, hb1]
  have hd1 : p.d1 = q.d1 := by
    rw [Romik.d1_eq_quarterPi_sub_b1_of_equations hp,
      Romik.d1_eq_quarterPi_sub_b1_of_equations hq, hb1]
  have hd2 : p.d2 = q.d2 := by
    rw [Romik.d2_eq_b2_add_quarterPi_correction_of_equations hp,
      Romik.d2_eq_b2_add_quarterPi_correction_of_equations hq, hb1, hb2]
  have he1 : p.e1 = q.e1 := by
    rw [Romik.e1_eq_a1_of_equations hp, Romik.e1_eq_a1_of_equations hq, ha1]
  have he2 : p.e2 = q.e2 := by
    rw [Romik.e2_eq_neg_a2_of_equations hp, Romik.e2_eq_neg_a2_of_equations hq, ha2]
  have hk11 : p.k11 = q.k11 := by
    have h5p := congrFun hp (5 : Fin 22)
    have h5q := congrFun hq (5 : Fin 22)
    change p.k11 - 1 + p.a1 = 0 at h5p
    change q.k11 - 1 + q.a1 = 0 at h5q
    linarith only [h5p, h5q, ha1]
  have hk12 : p.k12 = q.k12 := by
    rw [Romik.k12_eq_quarter_of_equations hp, Romik.k12_eq_quarter_of_equations hq]
  have hpath1 (t : ℝ) : Romik.path1 p t = Romik.path1 q t := by
    simp only [Romik.path1, ha1, ha2, hk11, hk12]
  have hj2 : Romik.path1 p (q.phi) = Romik.path2 p (q.phi) := by
    simpa only [hphi] using Romik.match_path12_of_equations hp
  have hx2 : Romik.path2 p (q.phi) = Romik.path2 q (q.phi) :=
    hj2.symm.trans ((hpath1 (q.phi)).trans (Romik.match_path12_of_equations hq))
  dsimp [Romik.path2, Romik.addK] at hx2
  simp only [hb1, hb2] at hx2
  have hk21 : p.k21 = q.k21 := add_left_cancel (congrArg Prod.fst hx2)
  have hk22 : p.k22 = q.k22 := add_left_cancel (congrArg Prod.snd hx2)
  have hpath2 (t : ℝ) : Romik.path2 p t = Romik.path2 q t := by
    simp only [Romik.path2, hb1, hb2, hk21, hk22]
  have hj3 : Romik.path2 p (q.theta) = Romik.path3 p (q.theta) := by
    simpa only [htheta] using Romik.match_path23_of_equations hp
  have hx3 : Romik.path3 p (q.theta) = Romik.path3 q (q.theta) :=
    hj3.symm.trans ((hpath2 (q.theta)).trans (Romik.match_path23_of_equations hq))
  dsimp [Romik.path3, Romik.addK] at hx3
  simp only [hc1, hc2] at hx3
  have hk31 : p.k31 = q.k31 := add_left_cancel (congrArg Prod.fst hx3)
  have hk32 : p.k32 = q.k32 := add_left_cancel (congrArg Prod.snd hx3)
  have hpath3 (t : ℝ) : Romik.path3 p t = Romik.path3 q t := by
    simp only [Romik.path3, hc1, hc2, hk31, hk32]
  have hj4 : Romik.path3 p (Real.pi / 2 - q.theta) = Romik.path4 p (Real.pi / 2 - q.theta) := by
    simpa only [htheta] using Romik.match_path34_of_equations hp
  have hx4 : Romik.path4 p (Real.pi / 2 - q.theta) = Romik.path4 q (Real.pi / 2 - q.theta) :=
    hj4.symm.trans ((hpath3 (Real.pi / 2 - q.theta)).trans (Romik.match_path34_of_equations hq))
  dsimp [Romik.path4, Romik.addK] at hx4
  simp only [hd1, hd2] at hx4
  have hk41 : p.k41 = q.k41 := add_left_cancel (congrArg Prod.fst hx4)
  have hk42 : p.k42 = q.k42 := add_left_cancel (congrArg Prod.snd hx4)
  have hpath4 (t : ℝ) : Romik.path4 p t = Romik.path4 q t := by
    simp only [Romik.path4, hd1, hd2, hk41, hk42]
  have hj5 : Romik.path4 p (Real.pi / 2 - q.phi) = Romik.path5 p (Real.pi / 2 - q.phi) := by
    simpa only [hphi] using Romik.match_path45_of_equations hp
  have hx5 : Romik.path5 p (Real.pi / 2 - q.phi) = Romik.path5 q (Real.pi / 2 - q.phi) :=
    hj5.symm.trans ((hpath4 (Real.pi / 2 - q.phi)).trans (Romik.match_path45_of_equations hq))
  dsimp [Romik.path5, Romik.addK] at hx5
  simp only [he1, he2] at hx5
  have hk51 : p.k51 = q.k51 := add_left_cancel (congrArg Prod.fst hx5)
  have hk52 : p.k52 = q.k52 := add_left_cancel (congrArg Prod.snd hx5)
  cases p
  cases q
  congr 1 <;> assumption

theorem dictionary_undictionary_of_equations {p : Romik.Params}
    (hp : Romik.Equations p) : dictionary (undictionary p) = p := by
  apply full_equations_injective (dictionary_equations _ (undictionary_equations hp)) hp
  exact undictionary_dictionary (undictionary p)

end GerverSofa.PartF.Phases
