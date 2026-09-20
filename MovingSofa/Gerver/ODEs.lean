import MovingSofa.Gerver.Contacts
import MovingSofa.Geometry.FrameCalculus

noncomputable section

namespace MovingSofa

def gerverStageContactDerivatives (i : Fin 5) (t : ℝ) : Fin 4 → ℝ :=
  ![inner ℝ (derivWithin (fun s ↦ paperGerverContacts s 0) (gerverStageIntervals i) t)
      (tangentVector (t : Real.Angle)),
    inner ℝ (derivWithin (fun s ↦ paperGerverContacts s 1) (gerverStageIntervals i) t)
      (tangentVector (t : Real.Angle)),
    inner ℝ (-(derivWithin (fun s ↦ paperGerverContacts s 2) (gerverStageIntervals i) t))
      (normalVector (t : Real.Angle)),
    inner ℝ (derivWithin (fun s ↦ paperGerverContacts s 3) (gerverStageIntervals i) t)
      (normalVector (t : Real.Angle))]

theorem gerver_stageODEs (i : Fin 5) (t : ℝ) (ht : t ∈ gerverStageIntervals i) :
    (gerverStageContactDerivatives i t 0, gerverStageContactDerivatives i t 2) =
      ![(0, gerverStageContactDerivatives i t 3),
        ((paperGerverVelocityComponents t).2,
          gerverStageContactDerivatives i t 3 - (paperGerverVelocityComponents t).1),
        ((paperGerverVelocityComponents t).2, -(paperGerverVelocityComponents t).1),
        (-gerverStageContactDerivatives i t 1 + (paperGerverVelocityComponents t).2,
          -(paperGerverVelocityComponents t).1),
        (-gerverStageContactDerivatives i t 1, 0)] i := by
  open GerverSofa.Romik GerverSofa.PartF.Coordinates in
  -- The certified direct parameter vector and the ordering of its switching angles.
  obtain ⟨p, hp⟩ : ∃ p : Params, GerverSofa.PartB.params = p := ⟨_, rfl⟩
  have hmem : p ∈ gerverDirectBox := hp ▸ GerverSofa.PartB.params_mem
  have heqs : gerverDirectEquations p := hp ▸ GerverSofa.PartB.params_equations
  obtain ⟨-, hphieq, hthetaeq, hphipos, hphitheta, hthetalt, -⟩ :=
    gerver_parameter_identification.1 p hmem heqs
  have hphi' : p.phi = GerversSofa.φ := hphieq.trans selected_phi
  have htheta' : p.theta = GerversSofa.θ := hthetaeq.trans selected_theta
  have h0 : (0 : ℝ) < p.phi := by rw [hphieq]; exact hphipos
  have h1 : p.phi < p.theta := by rw [hphieq, hthetaeq]; exact hphitheta
  have h2 : p.theta < Real.pi / 4 := by rw [hthetaeq]; exact hthetalt
  -- The five closed stage intervals in terms of the direct switching angles.
  have hI0 : gerverStageIntervals 0 = Set.Icc 0 p.phi := by
    simp [gerverStageIntervals, gerverStageTimes, hphi']
  have hI1 : gerverStageIntervals 1 = Set.Icc p.phi p.theta := by
    simp [gerverStageIntervals, gerverStageTimes, hphi', htheta']
  have hI2 : gerverStageIntervals 2 = Set.Icc p.theta (Real.pi / 2 - p.theta) := by
    simp [gerverStageIntervals, gerverStageTimes, htheta']
  have hI3 : gerverStageIntervals 3 =
      Set.Icc (Real.pi / 2 - p.theta) (Real.pi / 2 - p.phi) := by
    simp [gerverStageIntervals, gerverStageTimes, hphi', htheta']
  have hI4 : gerverStageIntervals 4 = Set.Icc (Real.pi / 2 - p.phi) (Real.pi / 2) := by
    simp [gerverStageIntervals, gerverStageTimes, hphi']
  have hval := paperGerverContactData_properties.2.2.2
  -- Frame orthonormality at the fixed angle `t`.
  have huu :
      inner ℝ (normalVector (t : Real.Angle)) (normalVector (t : Real.Angle)) = (1 : ℝ) :=
    inner_normalVector_self t
  have hvv :
      inner ℝ (tangentVector (t : Real.Angle)) (tangentVector (t : Real.Angle)) = (1 : ℝ) :=
    inner_tangentVector_self t
  have huv :
      inner ℝ (normalVector (t : Real.Angle)) (tangentVector (t : Real.Angle)) = (0 : ℝ) :=
    inner_normalVector_tangentVector t
  have hvu :
      inner ℝ (tangentVector (t : Real.Angle)) (normalVector (t : Real.Angle)) = (0 : ℝ) := by
    rw [real_inner_comm]; exact huv
  -- Derivatives of the ten branch coefficient functions, in one normal form.
  have hidt : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
  have hshape : ∀ (c₀ c₁ c₂ c₃ c₄ : ℝ) (f : ℝ → ℝ),
      (∀ s : ℝ,
        f s = c₀ + c₁ * s + c₂ * s * s + c₃ * Real.sin s + c₄ * Real.cos s) →
      HasDerivAt f (c₁ + 2 * c₂ * t + c₃ * Real.cos t - c₄ * Real.sin t) t := by
    intro c₀ c₁ c₂ c₃ c₄ f hf
    have h : HasDerivAt
        (fun s : ℝ => c₀ + c₁ * s + c₂ * s * s + c₃ * Real.sin s + c₄ * Real.cos s)
        (c₁ + 2 * c₂ * t + c₃ * Real.cos t - c₄ * Real.sin t) t := by
      refine ((((hasDerivAt_const t c₀).fun_add (hidt.const_mul c₁)).fun_add
        ((hidt.const_mul c₂).fun_mul hidt)).fun_add
        ((Real.hasDerivAt_sin t).const_mul c₃)).fun_add
        ((Real.hasDerivAt_cos t).const_mul c₄) |>.congr_deriv ?_
      ring
    exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => hf s)
  -- Unique differentiability of the closed stage interval at `t`.
  have g0 : (0 : ℝ) < GerversSofa.φ := by rw [← hphi']; exact h0
  have g1 : GerversSofa.φ < GerversSofa.θ := by rw [← hphi', ← htheta']; exact h1
  have g2 : GerversSofa.θ < Real.pi / 4 := by rw [← htheta']; exact h2
  have huniq : UniqueDiffWithinAt ℝ (gerverStageIntervals i) t := by
    fin_cases i
    · exact uniqueDiffOn_Icc g0 t ht
    · exact uniqueDiffOn_Icc g1 t ht
    · exact uniqueDiffOn_Icc
        (show GerversSofa.θ < Real.pi / 2 - GerversSofa.θ by linarith) t ht
    · exact uniqueDiffOn_Icc
        (show Real.pi / 2 - GerversSofa.θ < Real.pi / 2 - GerversSofa.φ by linarith) t ht
    · exact uniqueDiffOn_Icc
        (show Real.pi / 2 - GerversSofa.φ < Real.pi / 2 by linarith) t ht
  -- The frame computation: the four contact derivatives in terms of `α, β, α', β'`.
  have hcore : ∀ (X : ℝ → Point) (X' : Point) (A B : ℝ → ℝ) (a' b' : ℝ),
      HasDerivAt X X' t →
      inner ℝ X' (normalVector (t : Real.Angle)) = A t →
      inner ℝ X' (tangentVector (t : Real.Angle)) = B t →
      HasDerivAt A a' t → HasDerivAt B b' t →
      (∀ r ∈ gerverStageIntervals i, paperGerverPath r = X r) →
      (∀ r ∈ gerverStageIntervals i, paperGerverVelocityComponents r = (A r, B r)) →
      gerverStageContactDerivatives i t 0 = B t + a' + 1 ∧
      gerverStageContactDerivatives i t 1 = B t + a' ∧
      gerverStageContactDerivatives i t 2 = b' + 1 - A t ∧
      gerverStageContactDerivatives i t 3 = A t - b' := by
    intro X X' A B a' b' hX hXu hXv hA hB hpath hvel
    have hn : HasDerivAt (fun s : ℝ => normalVector (s : Real.Angle))
        (tangentVector (t : Real.Angle)) t := hasDerivAt_normalVector t
    have hg : HasDerivAt (fun s : ℝ => tangentVector (s : Real.Angle))
        (-normalVector (t : Real.Angle)) t := hasDerivAt_tangentVector t
    have hAv := hA.fun_smul hg
    have hBn := hB.fun_smul hn
    have hc0 : HasDerivWithinAt (fun s => paperGerverContacts s 0)
        (X' + (A t • (-normalVector (t : Real.Angle)) + a' • tangentVector (t : Real.Angle)) +
          tangentVector (t : Real.Angle)) (gerverStageIntervals i) t := by
      refine ((hX.fun_add hAv).fun_add hn).hasDerivWithinAt.congr (fun r hr => ?_) ?_
      · simp only [paperGerverContacts, Matrix.cons_val_zero, hpath r hr, hvel r hr]
      · simp only [paperGerverContacts, Matrix.cons_val_zero, hpath t ht, hvel t ht]
    have hc1 : HasDerivWithinAt (fun s => paperGerverContacts s 1)
        (X' + (A t • (-normalVector (t : Real.Angle)) + a' • tangentVector (t : Real.Angle)))
        (gerverStageIntervals i) t := by
      refine (hX.fun_add hAv).hasDerivWithinAt.congr (fun r hr => ?_) ?_
      · simp only [paperGerverContacts, hpath r hr, hvel r hr]
        rfl
      · simp only [paperGerverContacts, hpath t ht, hvel t ht]
        rfl
    have hc2 : HasDerivWithinAt (fun s => paperGerverContacts s 2)
        (X' - (B t • tangentVector (t : Real.Angle) + b' • normalVector (t : Real.Angle)) +
          -normalVector (t : Real.Angle)) (gerverStageIntervals i) t := by
      refine ((hX.fun_sub hBn).fun_add hg).hasDerivWithinAt.congr (fun r hr => ?_) ?_
      · simp only [paperGerverContacts, hpath r hr, hvel r hr]
        rfl
      · simp only [paperGerverContacts, hpath t ht, hvel t ht]
        rfl
    have hc3 : HasDerivWithinAt (fun s => paperGerverContacts s 3)
        (X' - (B t • tangentVector (t : Real.Angle) + b' • normalVector (t : Real.Angle)))
        (gerverStageIntervals i) t := by
      refine (hX.fun_sub hBn).hasDerivWithinAt.congr (fun r hr => ?_) ?_
      · simp only [paperGerverContacts, hpath r hr, hvel r hr]
        rfl
      · simp only [paperGerverContacts, hpath t ht, hvel t ht]
        rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · show inner ℝ (derivWithin (fun s => paperGerverContacts s 0) (gerverStageIntervals i) t)
        (tangentVector (t : Real.Angle)) = B t + a' + 1
      rw [hc0.derivWithin huniq]
      simp only [inner_add_left, real_inner_smul_left, inner_neg_left, hXv, huv, hvv]
      ring
    · show inner ℝ (derivWithin (fun s => paperGerverContacts s 1) (gerverStageIntervals i) t)
        (tangentVector (t : Real.Angle)) = B t + a'
      rw [hc1.derivWithin huniq]
      simp only [inner_add_left, real_inner_smul_left, inner_neg_left, hXv, huv, hvv]
      ring
    · show inner ℝ (-derivWithin (fun s => paperGerverContacts s 2) (gerverStageIntervals i) t)
        (normalVector (t : Real.Angle)) = b' + 1 - A t
      rw [hc2.derivWithin huniq]
      simp only [inner_neg_left, inner_add_left, inner_sub_left, real_inner_smul_left, hXu, hvu,
        huu]
      ring
    · show inner ℝ (derivWithin (fun s => paperGerverContacts s 3) (gerverStageIntervals i) t)
        (normalVector (t : Real.Angle)) = A t - b'
      rw [hc3.derivWithin huniq]
      simp only [inner_sub_left, inner_add_left, real_inner_smul_left, hXu, hvu, huu]
      ring
  fin_cases i
  · -- Stage 1
    have hvel : ∀ r ∈ gerverStageIntervals 0,
        paperGerverVelocityComponents r = alphaBeta1 p r := by
      intro r hr
      rw [hval 0 r hr]
      simp [gerverBranchVelocityComponents, hp]
    obtain ⟨e0, e1, e2, e3⟩ := hcore (fun s => toPlane (path1 p s))
      (toPlane (rot t (alphaBeta1 p t))) (fun s => (alphaBeta1 p s).1)
      (fun s => (alphaBeta1 p s).2) _ _ (hasDerivAt_toPlane (hasDerivAt_path1 p t))
      (inner_toPlane_rot_normalVector t _) (inner_toPlane_rot_tangentVector t _)
      (hshape (1 / 2) 0 0 (-2 * p.a1) (2 * p.a2) _ fun s => by dsimp [alphaBeta1]; ring)
      (hshape (-1) 0 0 (2 * p.a2) (2 * p.a1) _ fun s => by dsimp [alphaBeta1]; ring)
      (fun r hr => by
        show toPlane (path GerverSofa.PartB.params r) = toPlane (path1 p r)
        rw [hp]
        exact congrArg toPlane (path_eq_path1_of_mem_Icc p (hI0 ▸ hr)))
      (fun r hr => hvel r hr)
    rw [Prod.mk.injEq, e0, e2, e3]
    refine ⟨?_, ?_⟩ <;> dsimp [alphaBeta1] <;> ring
  · -- Stage 2
    have hvel : ∀ r ∈ gerverStageIntervals 1,
        paperGerverVelocityComponents r = alphaBeta2 p r := by
      intro r hr
      rw [hval 1 r hr]
      simp [gerverBranchVelocityComponents, hp]
    obtain ⟨e0, e1, e2, e3⟩ := hcore (fun s => toPlane (path2 p s))
      (toPlane (rot t (alphaBeta2 p t))) (fun s => (alphaBeta2 p s).1)
      (fun s => (alphaBeta2 p s).2) _ _ (hasDerivAt_toPlane (hasDerivAt_path2 p t))
      (inner_toPlane_rot_normalVector t _) (inner_toPlane_rot_tangentVector t _)
      (hshape (1 + 2 * p.b1) (-1) 0 0 0 _ fun s => by dsimp [alphaBeta2]; ring)
      (hshape (p.b2 + 1 / 2) p.b1 (-(1 / 4)) 0 0 _ fun s => by dsimp [alphaBeta2]; ring)
      (fun r hr => by
        show toPlane (path GerverSofa.PartB.params r) = toPlane (path2 p r)
        rw [hp]
        exact congrArg toPlane (path_eq_path2_of_mem_Icc heqs (hI1 ▸ hr)))
      (fun r hr => hvel r hr)
    rw [Prod.mk.injEq, hvel t ht, e0, e2, e3]
    refine ⟨?_, ?_⟩ <;> dsimp [alphaBeta2] <;> ring
  · -- Stage 3
    have hvel : ∀ r ∈ gerverStageIntervals 2,
        paperGerverVelocityComponents r = alphaBeta3 p r := by
      intro r hr
      rw [hval 2 r hr]
      simp [gerverBranchVelocityComponents, hp]
    obtain ⟨e0, e1, e2, e3⟩ := hcore (fun s => toPlane (path3 p s))
      (toPlane (rot t (alphaBeta3 p t))) (fun s => (alphaBeta3 p s).1)
      (fun s => (alphaBeta3 p s).2) _ _ (hasDerivAt_toPlane (hasDerivAt_path3 p t))
      (inner_toPlane_rot_normalVector t _) (inner_toPlane_rot_tangentVector t _)
      (hshape (-1 - p.c2) (-1) 0 0 0 _ fun s => by dsimp [alphaBeta3]; ring)
      (hshape (1 + p.c1) (-1) 0 0 0 _ fun s => by dsimp [alphaBeta3]; ring)
      (fun r hr => by
        show toPlane (path GerverSofa.PartB.params r) = toPlane (path3 p r)
        rw [hp]
        exact congrArg toPlane (path_eq_path3_of_mem_Icc heqs h1 (hI2 ▸ hr)))
      (fun r hr => hvel r hr)
    rw [Prod.mk.injEq, hvel t ht, e0, e2]
    refine ⟨?_, ?_⟩ <;> dsimp [alphaBeta3] <;> ring
  · -- Stage 4
    have hvel : ∀ r ∈ gerverStageIntervals 3,
        paperGerverVelocityComponents r = alphaBeta4 p r := by
      intro r hr
      rw [hval 3 r hr]
      simp [gerverBranchVelocityComponents, hp]
    obtain ⟨e0, e1, e2, e3⟩ := hcore (fun s => toPlane (path4 p s))
      (toPlane (rot t (alphaBeta4 p t))) (fun s => (alphaBeta4 p s).1)
      (fun s => (alphaBeta4 p s).2) _ _ (hasDerivAt_toPlane (hasDerivAt_path4 p t))
      (inner_toPlane_rot_normalVector t _) (inner_toPlane_rot_tangentVector t _)
      (hshape (-p.d2 - 1 / 2) (-p.d1) (1 / 4) 0 0 _ fun s => by dsimp [alphaBeta4]; ring)
      (hshape (2 * p.d1 - 1) (-1) 0 0 0 _ fun s => by dsimp [alphaBeta4]; ring)
      (fun r hr => by
        show toPlane (path GerverSofa.PartB.params r) = toPlane (path4 p r)
        rw [hp]
        exact congrArg toPlane (path_eq_path4_of_mem_Icc heqs h1 h2 (hI3 ▸ hr)))
      (fun r hr => hvel r hr)
    rw [Prod.mk.injEq, hvel t ht, e0, e1, e2]
    refine ⟨?_, ?_⟩ <;> dsimp [alphaBeta4] <;> ring
  · -- Stage 5
    have hvel : ∀ r ∈ gerverStageIntervals 4,
        paperGerverVelocityComponents r = alphaBeta5 p r := by
      intro r hr
      rw [hval 4 r hr]
      simp [gerverBranchVelocityComponents, hp]
    obtain ⟨e0, e1, e2, e3⟩ := hcore (fun s => toPlane (path5 p s))
      (toPlane (rot t (alphaBeta5 p t))) (fun s => (alphaBeta5 p s).1)
      (fun s => (alphaBeta5 p s).2) _ _ (hasDerivAt_toPlane (hasDerivAt_path5 p t))
      (inner_toPlane_rot_normalVector t _) (inner_toPlane_rot_tangentVector t _)
      (hshape 1 0 0 (-2 * p.e1) (2 * p.e2) _ fun s => by dsimp [alphaBeta5]; ring)
      (hshape (-(1 / 2)) 0 0 (2 * p.e2) (2 * p.e1) _ fun s => by dsimp [alphaBeta5]; ring)
      (fun r hr => by
        show toPlane (path GerverSofa.PartB.params r) = toPlane (path5 p r)
        rw [hp]
        exact congrArg toPlane (path_eq_path5_of_mem_Icc heqs h1 h2 (hI4 ▸ hr)))
      (fun r hr => hvel r hr)
    rw [Prod.mk.injEq, e0, e1, e2]
    refine ⟨?_, ?_⟩ <;> dsimp [alphaBeta5] <;> ring

end MovingSofa
