import GerverSofa.KernelOnly.PartF.F01PhaseAlgebra

/-!
# F05: the four-parameter dictionary satisfies the full 22 equations

These polynomial certificates use the four reduced equations and the two
trigonometric circle identities. No box membership or uniqueness is assumed.
They do not identify the dictionary with the independently certified 22D root.
The module is independent of the F04 integral evaluation.
-/

noncomputable section
set_option maxHeartbeats 2000000

namespace GerverSofa.PartF.Phases

theorem dictionary_equations (d : Reduced.Params) (hd : Reduced.Equations d) :
    Romik.Equations (dictionary d) := by
  have h1 := congrFun hd (0 : Fin 4)
  have h2 := congrFun hd (1 : Fin 4)
  have h3 := congrFun hd (2 : Fin 4)
  have h4 := congrFun hd (3 : Fin 4)
  change d.a * (Real.cos d.theta - Real.cos d.phi) -
    2 * d.b * Real.sin d.phi + (d.theta - d.phi - 1) * Real.cos d.theta -
    Real.sin d.theta + Real.cos d.phi + Real.sin d.phi = 0 at h1
  change d.a * (3 * Real.sin d.theta + Real.sin d.phi) -
    2 * d.b * Real.cos d.phi + 3 * (d.theta - d.phi - 1) * Real.sin d.theta +
    3 * Real.cos d.theta - Real.sin d.phi + Real.cos d.phi = 0 at h2
  change d.a * Real.cos d.phi - Real.sin d.phi - 1 / 2 +
    1 / 2 * Real.cos d.phi - d.b * Real.sin d.phi = 0 at h3
  change d.a + Real.pi / 2 - d.phi - d.theta - d.b +
    1 / 2 * (d.theta - d.phi) * (1 + d.a) +
    1 / 4 * (d.theta - d.phi) * (d.theta - d.phi) = 0 at h4
  have hcphi := Real.sin_sq_add_cos_sq d.phi
  have hctheta := Real.sin_sq_add_cos_sq d.theta
  change Romik.system (dictionary d) = 0
  funext i
  fin_cases i
  -- Row 0: exact scalar certificate.
  · change (dictionary d).e1 - (dictionary d).a1 = 0
    dsimp [dictionary, T] <;> ring
  -- Row 1: exact scalar certificate.
  · change (dictionary d).e2 + (dictionary d).a2 = 0
    dsimp [dictionary, T] <;> ring
  -- Row 2: exact scalar certificate.
  · change (dictionary d).d1 + (dictionary d).b1 - Real.pi / 4 = 0
    dsimp [dictionary, T] <;> ring
  -- Row 3: exact scalar certificate.
  · change (dictionary d).d2 - (dictionary d).b2 - Real.pi / 4 * (2 * (dictionary d).b1 - Real.pi / 4) = 0
    dsimp [dictionary, T] <;> ring
  -- Row 4: exact scalar certificate.
  · change (dictionary d).c2 - (dictionary d).c1 + Real.pi / 2 = 0
    dsimp [dictionary, T] <;> ring
  -- Row 5: exact scalar certificate.
  · change (dictionary d).k11 - 1 + (dictionary d).a1 = 0
    dsimp [dictionary, T] <;> ring
  -- Row 6: exact scalar certificate.
  · change (dictionary d).k12 - 1 / 4 = 0
    dsimp [dictionary, T] <;> ring
  -- Row 7: exact scalar certificate.
  · change (dictionary d).a2 + 1 / 4 = 0
    dsimp [dictionary, T] <;> ring
  -- Row 8: exact scalar certificate.
  · change (Romik.path1 (dictionary d) (d.phi)).1 - (Romik.path2 (dictionary d) (d.phi)).1 = 0
    dsimp [Romik.path1, Romik.path2, Romik.path3, Romik.path4, Romik.path5,
      Romik.rot, Romik.addK, Romik.alphaBeta1, Romik.alphaBeta2, Romik.alphaBeta3,
      dictionary, U1, U2, U3, U4, V1, V2, V3, V4, hStar, T]
    linear_combination ((Real.sin d.phi) ^ 2) * h2 +
      ((Real.sin d.phi) * (Real.cos d.phi)) * h3 +
      (-1 * (d.a) * (Real.sin d.phi) + (-3 / 2 : ℝ) * (d.a) * (Real.sin d.theta) + (3 / 2 : ℝ) * (d.b) * (Real.cos d.phi) + (3 / 2 : ℝ) * (d.phi) * (Real.sin d.theta) + (-3 / 2 : ℝ) * (d.theta) * (Real.sin d.theta) + (1 / 4 : ℝ) * (Real.sin d.phi) + (3 / 2 : ℝ) * (Real.sin d.theta) + (-3 / 2 : ℝ) * (Real.cos d.theta)) * hcphi
  -- Row 9: exact scalar certificate.
  · change (Romik.path1 (dictionary d) (d.phi)).2 - (Romik.path2 (dictionary d) (d.phi)).2 = 0
    dsimp [Romik.path1, Romik.path2, Romik.path3, Romik.path4, Romik.path5,
      Romik.rot, Romik.addK, Romik.alphaBeta1, Romik.alphaBeta2, Romik.alphaBeta3,
      dictionary, U1, U2, U3, U4, V1, V2, V3, V4, hStar, T]
    linear_combination (-1 * (Real.sin d.phi) * (Real.cos d.phi)) * h2 +
      ((Real.sin d.phi) ^ 2 + -1) * h3 +
      ((d.b) * (Real.sin d.phi) + (Real.sin d.phi) + (1 / 4 : ℝ)) * hcphi
  -- Row 10: exact scalar certificate.
  · change (Romik.rot (d.phi) (Romik.alphaBeta1 (dictionary d) (d.phi))).1 - (Romik.rot (d.phi) (Romik.alphaBeta2 (dictionary d) (d.phi))).1 = 0
    dsimp [Romik.path1, Romik.path2, Romik.path3, Romik.path4, Romik.path5,
      Romik.rot, Romik.addK, Romik.alphaBeta1, Romik.alphaBeta2, Romik.alphaBeta3,
      dictionary, U1, U2, U3, U4, V1, V2, V3, V4, hStar, T]
    linear_combination (2 * (Real.sin d.phi) * (Real.cos d.phi)) * h2 +
      (-2 * (Real.sin d.phi) ^ 2 + 1) * h3 +
      (-2 * (d.b) * (Real.sin d.phi) + -2 * (Real.sin d.phi) + (-1 / 2 : ℝ)) * hcphi
  -- Row 11: exact scalar certificate.
  · change (Romik.rot (d.phi) (Romik.alphaBeta1 (dictionary d) (d.phi))).2 - (Romik.rot (d.phi) (Romik.alphaBeta2 (dictionary d) (d.phi))).2 = 0
    dsimp [Romik.path1, Romik.path2, Romik.path3, Romik.path4, Romik.path5,
      Romik.rot, Romik.addK, Romik.alphaBeta1, Romik.alphaBeta2, Romik.alphaBeta3,
      dictionary, U1, U2, U3, U4, V1, V2, V3, V4, hStar, T]
    linear_combination (2 * (Real.sin d.phi) ^ 2 + -1) * h2 +
      (2 * (Real.sin d.phi) * (Real.cos d.phi)) * h3 +
      (-2 * (d.a) * (Real.sin d.phi) + -3 * (d.a) * (Real.sin d.theta) + 3 * (d.b) * (Real.cos d.phi) + 3 * (d.phi) * (Real.sin d.theta) + -3 * (d.theta) * (Real.sin d.theta) + (1 / 2 : ℝ) * (Real.sin d.phi) + 3 * (Real.sin d.theta) + -3 * (Real.cos d.theta)) * hcphi
  -- Row 12: exact scalar certificate.
  · change (Romik.path2 (dictionary d) (d.theta)).1 - (Romik.path3 (dictionary d) (d.theta)).1 = 0
    dsimp [Romik.path1, Romik.path2, Romik.path3, Romik.path4, Romik.path5,
      Romik.rot, Romik.addK, Romik.alphaBeta1, Romik.alphaBeta2, Romik.alphaBeta3,
      dictionary, U1, U2, U3, U4, V1, V2, V3, V4, hStar, T]
    linear_combination (-1 * (Real.cos d.theta)) * h4
  -- Row 13: exact scalar certificate.
  · change (Romik.path2 (dictionary d) (d.theta)).2 - (Romik.path3 (dictionary d) (d.theta)).2 = 0
    dsimp [Romik.path1, Romik.path2, Romik.path3, Romik.path4, Romik.path5,
      Romik.rot, Romik.addK, Romik.alphaBeta1, Romik.alphaBeta2, Romik.alphaBeta3,
      dictionary, U1, U2, U3, U4, V1, V2, V3, V4, hStar, T]
    linear_combination (-1 * (Real.sin d.theta)) * h4
  -- Row 14: exact scalar certificate.
  · change (Romik.rot (d.theta) (Romik.alphaBeta2 (dictionary d) (d.theta))).1 - (Romik.rot (d.theta) (Romik.alphaBeta3 (dictionary d) (d.theta))).1 = 0
    dsimp [Romik.path1, Romik.path2, Romik.path3, Romik.path4, Romik.path5,
      Romik.rot, Romik.addK, Romik.alphaBeta1, Romik.alphaBeta2, Romik.alphaBeta3,
      dictionary, U1, U2, U3, U4, V1, V2, V3, V4, hStar, T]
    linear_combination ((Real.sin d.theta)) * h4
  -- Row 15: exact scalar certificate.
  · change (Romik.rot (d.theta) (Romik.alphaBeta2 (dictionary d) (d.theta))).2 - (Romik.rot (d.theta) (Romik.alphaBeta3 (dictionary d) (d.theta))).2 = 0
    dsimp [Romik.path1, Romik.path2, Romik.path3, Romik.path4, Romik.path5,
      Romik.rot, Romik.addK, Romik.alphaBeta1, Romik.alphaBeta2, Romik.alphaBeta3,
      dictionary, U1, U2, U3, U4, V1, V2, V3, V4, hStar, T]
    linear_combination (-1 * (Real.cos d.theta)) * h4
  -- Row 16: exact scalar certificate.
  · change (Romik.path3 (dictionary d) (Real.pi / 2 - d.theta)).1 - (Romik.path4 (dictionary d) (Real.pi / 2 - d.theta)).1 = 0
    dsimp [Romik.path1, Romik.path2, Romik.path3, Romik.path4, Romik.path5,
      Romik.rot, Romik.addK, Romik.alphaBeta1, Romik.alphaBeta2, Romik.alphaBeta3,
      dictionary, U1, U2, U3, U4, V1, V2, V3, V4, hStar, T]
    simp only [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
    linear_combination (-1 * (Real.cos d.theta)) * h4
  -- Row 17: exact scalar certificate.
  · change (Romik.path3 (dictionary d) (Real.pi / 2 - d.theta)).2 - (Romik.path4 (dictionary d) (Real.pi / 2 - d.theta)).2 = 0
    dsimp [Romik.path1, Romik.path2, Romik.path3, Romik.path4, Romik.path5,
      Romik.rot, Romik.addK, Romik.alphaBeta1, Romik.alphaBeta2, Romik.alphaBeta3,
      dictionary, U1, U2, U3, U4, V1, V2, V3, V4, hStar, T]
    simp only [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
    linear_combination ((Real.sin d.theta)) * h4
  -- Row 18: exact scalar certificate.
  · change (Romik.path4 (dictionary d) (Real.pi / 2 - d.phi)).1 - (Romik.path5 (dictionary d) (Real.pi / 2 - d.phi)).1 = 0
    dsimp [Romik.path1, Romik.path2, Romik.path3, Romik.path4, Romik.path5,
      Romik.rot, Romik.addK, Romik.alphaBeta1, Romik.alphaBeta2, Romik.alphaBeta3,
      dictionary, U1, U2, U3, U4, V1, V2, V3, V4, hStar, T]
    simp only [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
    linear_combination ((Real.sin d.phi) ^ 2 + -1) * h2 +
      ((Real.sin d.phi) * (Real.cos d.phi)) * h3 +
      (-1 * (d.a) * (Real.sin d.phi) + (-3 / 2 : ℝ) * (d.a) * (Real.sin d.theta) + (3 / 2 : ℝ) * (d.b) * (Real.cos d.phi) + (3 / 2 : ℝ) * (d.phi) * (Real.sin d.theta) + (-3 / 2 : ℝ) * (d.theta) * (Real.sin d.theta) + (1 / 4 : ℝ) * (Real.sin d.phi) + (3 / 2 : ℝ) * (Real.sin d.theta) + (-3 / 2 : ℝ) * (Real.cos d.theta)) * hcphi
  -- Row 19: exact scalar certificate.
  · change (Romik.path4 (dictionary d) (Real.pi / 2 - d.phi)).2 - (Romik.path5 (dictionary d) (Real.pi / 2 - d.phi)).2 = 0
    dsimp [Romik.path1, Romik.path2, Romik.path3, Romik.path4, Romik.path5,
      Romik.rot, Romik.addK, Romik.alphaBeta1, Romik.alphaBeta2, Romik.alphaBeta3,
      dictionary, U1, U2, U3, U4, V1, V2, V3, V4, hStar, T]
    simp only [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
    linear_combination ((Real.sin d.phi) * (Real.cos d.phi)) * h2 +
      (-1 * (Real.sin d.phi) ^ 2 + 1) * h3 +
      (-1 * (d.b) * (Real.sin d.phi) + -1 * (Real.sin d.phi) + (-1 / 4 : ℝ)) * hcphi
  -- Row 20: exact scalar certificate.
  · change (Romik.path1 (dictionary d) d.phi).1 - ((Romik.path3 (dictionary d) (Real.pi / 2 - d.theta)).1 - (Romik.alphaBeta3 (dictionary d) (Real.pi / 2 - d.theta)).1 * Real.sin (Real.pi / 2 - d.theta)) = 0
    dsimp [Romik.path1, Romik.path2, Romik.path3, Romik.path4, Romik.path5,
      Romik.rot, Romik.addK, Romik.alphaBeta1, Romik.alphaBeta2, Romik.alphaBeta3,
      dictionary, U1, U2, U3, U4, V1, V2, V3, V4, hStar, T]
    simp only [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
    linear_combination ((Real.sin d.phi) ^ 2 + (-1 / 2 : ℝ)) * h2 +
      ((Real.sin d.phi) * (Real.cos d.phi)) * h3 +
      (-1 * (d.a) * (Real.sin d.phi) + (-3 / 2 : ℝ) * (d.a) * (Real.sin d.theta) + (3 / 2 : ℝ) * (d.b) * (Real.cos d.phi) + (3 / 2 : ℝ) * (d.phi) * (Real.sin d.theta) + (-3 / 2 : ℝ) * (d.theta) * (Real.sin d.theta) + (1 / 4 : ℝ) * (Real.sin d.phi) + (3 / 2 : ℝ) * (Real.sin d.theta) + (-3 / 2 : ℝ) * (Real.cos d.theta)) * hcphi
  -- Row 21: exact scalar certificate.
  · change (Romik.path1 (dictionary d) d.phi).2 - ((Romik.path3 (dictionary d) (Real.pi / 2 - d.theta)).2 + (Romik.alphaBeta3 (dictionary d) (Real.pi / 2 - d.theta)).1 * Real.cos (Real.pi / 2 - d.theta)) = 0
    dsimp [Romik.path1, Romik.path2, Romik.path3, Romik.path4, Romik.path5,
      Romik.rot, Romik.addK, Romik.alphaBeta1, Romik.alphaBeta2, Romik.alphaBeta3,
      dictionary, U1, U2, U3, U4, V1, V2, V3, V4, hStar, T]
    simp only [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
    linear_combination ((-1 / 2 : ℝ)) * h1 +
      (-1 * (Real.sin d.phi) * (Real.cos d.phi)) * h2 +
      ((Real.sin d.phi) ^ 2 + -1) * h3 +
      ((d.b) * (Real.sin d.phi) + (Real.sin d.phi) + (1 / 4 : ℝ)) * hcphi

/-- Read back the four free parameters from the 22D representation. -/
def undictionary (p : Romik.Params) : Reduced.Params where
  a := p.phi - 1 - 2 * p.b1
  b := p.b2 + 1 / 2 - (1 + (p.phi - 1 - 2 * p.b1)) * p.phi / 2 + p.phi ^ 2 / 4
  phi := p.phi
  theta := p.theta

theorem undictionary_dictionary (d : Reduced.Params) :
    undictionary (dictionary d) = d := by
  rcases d with ⟨a, b, phi, theta⟩
  dsimp [undictionary, dictionary]
  congr 1 <;> ring

end GerverSofa.PartF.Phases
