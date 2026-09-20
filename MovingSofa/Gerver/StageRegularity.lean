import MovingSofa.Gerver.Contacts
import MovingSofa.Geometry.FrameCalculus
import MovingSofa.Curve.SmoothIntervalPaths

/-!
# Regularity of the certified Gerver stage data

The five Gerver stages are nondegenerate: the six stage endpoints increase strictly from `0`
to `π / 2` (`gerverStageTimes_strictMono`), and `gerverStageIntervals_zero` through
`gerverStageIntervals_four` name the resulting closed stage intervals.  The certified direct
path is continuously differentiable on the whole rotation interval
(`contDiff_paperGerverPath`), while each contact curve is only continuous globally
(`continuous_paperGerverContact`) and continuously differentiable on a single stage
(`contDiffOn_paperGerverContact`).  Gluing two consecutive stages presents the two inner
contact curves on the parameter ranges where they touch the cap as continuous paths of bounded
variation (`gerverRightContactBV`, `gerverLeftContactBV`).

The second half of the file differentiates the two inner contact curves stagewise.  Writing
the velocity components of the direct path as `(α, β)`, the contact formulas are
`B = x + α v` and `D = x - β u`, so the product rule and the frame derivatives
`hasDerivAt_normalVector`, `hasDerivAt_tangentVector` give
`B' = (β + α') v` and `D' = (α - β') u`
(`hasDerivWithinAt_paperGerverContacts_one`, `hasDerivWithinAt_paperGerverContacts_three`).
Feeding the five analytic stage branches of `paperGerverContactData_properties` into these
two lemmas yields the signs of the two speeds on the stages where they are needed
(`hasDerivWithinAt_paperGerverContacts_one_neg_smul`,
`hasDerivWithinAt_paperGerverContacts_three_pos_smul`); the two nonconstant coefficients are
signed by the coarse box bounds `gerverDirectBox_b1_lower_bound`,
`gerverDirectBox_d1_upper_bound` and `gerverStageTimes_two_le_seven_div_ten`.

The last two sections record the consequences used downstream: the frame coordinates
`s ↦ x s ⋅ u_s` and `s ↦ x s ⋅ v_s` of the direct path are differentiable with derivatives
`B ⋅ v` and `-D ⋅ u` (`hasDerivAt_inner_paperGerverPath_normalVector`,
`hasDerivAt_inner_paperGerverPath_tangentVector`), and against a fixed frame direction outside
the stage the two inner contact curves are strictly monotone on each stage
(`strictAntiOn_inner_paperGerverContacts_three`, `strictMonoOn_inner_paperGerverContacts_one`).
-/

noncomputable section

namespace MovingSofa

/-- The six Gerver stage endpoints increase strictly along the rotation interval. -/
theorem gerverStageTimes_strictMono : StrictMono gerverStageTimes := by
  obtain ⟨-, -, -, hpos, hlt, hqt, -⟩ := gerver_parameter_identification.1
    GerverSofa.PartB.params GerverSofa.PartB.params_mem GerverSofa.PartB.params_equations
  rw [selected_phi] at hpos
  rw [selected_phi, selected_theta] at hlt
  rw [selected_theta] at hqt
  refine Fin.strictMono_iff_lt_succ.mpr fun i ↦ ?_
  fin_cases i
  · show gerverStageTimes 0 < gerverStageTimes 1
    simp only [gerverStageTimes, Matrix.cons_val_zero, Matrix.cons_val_one]
    linarith
  · show gerverStageTimes 1 < gerverStageTimes 2
    simp only [gerverStageTimes, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    linarith
  · show gerverStageTimes 2 < gerverStageTimes 3
    simp only [gerverStageTimes, Matrix.cons_val]
    linarith
  · show gerverStageTimes 3 < gerverStageTimes 4
    simp only [gerverStageTimes, Matrix.cons_val]
    linarith
  · show gerverStageTimes 4 < gerverStageTimes 5
    simp only [gerverStageTimes, Matrix.cons_val]
    linarith

/-- The second Gerver stage time is at most `7/10`.  This coarse bound on the certified
switching angle `θ` is what the stage speed estimates below consume. -/
theorem gerverStageTimes_two_le_seven_div_ten : gerverStageTimes 2 ≤ (7 : ℝ) / 10 := by
  have h := GerverSofa.PartB.theta_bounds.2
  rw [gerverStageTimes_two]
  norm_num at h ⊢
  linarith

/-- The first Gerver stage runs between the first two stage times. -/
theorem gerverStageIntervals_zero :
    gerverStageIntervals 0 = Set.Icc (gerverStageTimes 0) (gerverStageTimes 1) := rfl

/-- The second Gerver stage runs between the second and third stage times. -/
theorem gerverStageIntervals_one :
    gerverStageIntervals 1 = Set.Icc (gerverStageTimes 1) (gerverStageTimes 2) := rfl

/-- The fourth Gerver stage runs between the fourth and fifth stage times. -/
theorem gerverStageIntervals_three :
    gerverStageIntervals 3 = Set.Icc (gerverStageTimes 3) (gerverStageTimes 4) := rfl

/-- The fifth Gerver stage runs between the last two stage times. -/
theorem gerverStageIntervals_four :
    gerverStageIntervals 4 = Set.Icc (gerverStageTimes 4) (gerverStageTimes 5) := rfl

/-- The certified direct Gerver path is continuously differentiable. -/
theorem contDiff_paperGerverPath : ContDiff ℝ 1 paperGerverPath := by
  obtain ⟨hC1, -, -⟩ := gerver_direct_path_regularity GerverSofa.PartB.params
    GerverSofa.PartB.params_mem GerverSofa.PartB.params_equations
  obtain ⟨L, hL⟩ : ∃ L : GerverSofa.Point →L[ℝ] Point,
      ⇑L = GerverSofa.PartF.Coordinates.toPlane :=
    ⟨{ toLinearMap := GerverSofa.PartF.Coordinates.linearEquiv.toLinearMap
       cont := GerverSofa.PartF.Coordinates.continuous_toPlane }, rfl⟩
  have hcomp : paperGerverPath = ⇑L ∘ GerverSofa.Romik.path GerverSofa.PartB.params := by
    rw [hL]
    rfl
  rw [hcomp]
  exact L.contDiff.comp hC1

/-- Each Gerver contact curve is continuous. -/
theorem continuous_paperGerverContact (i : Fin 4) :
    Continuous fun t : ℝ ↦ paperGerverContacts t i :=
  (continuous_apply i).comp paperGerverContactData_properties.2.1

/-- Each Gerver contact curve is continuously differentiable on each closed stage interval. -/
theorem contDiffOn_paperGerverContact (i : Fin 4) (j : Fin 5) :
    ContDiffOn ℝ 1 (fun t : ℝ ↦ paperGerverContacts t i) (gerverStageIntervals j) :=
  (contDiffOn_pi.mp (paperGerverContactData_properties.2.2.1 j) i).of_le (by norm_num)

/-! ### The two inner contact curves as bounded-variation paths -/

/-- The second Gerver contact curve, on the two stages `[t₃, t₅]` where it is an inner contact
of the cap, as a continuous path of bounded variation. -/
def gerverRightContactBV : ContinuousBVPaths (gerverStageTimes 3) (gerverStageTimes 5) :=
  continuousBVOfContDiffOnIccUnionIcc (fun t ↦ paperGerverContacts t 1)
    (gerverStageTimes_strictMono (show (3 : Fin 6) < 4 by decide)).le
    (gerverStageTimes_strictMono (show (4 : Fin 6) < 5 by decide)).le
    (contDiffOn_paperGerverContact 1 3) (contDiffOn_paperGerverContact 1 4)

/-- The fourth Gerver contact curve, on the two stages `[t₀, t₂]` where it is an inner contact
of the cap, as a continuous path of bounded variation. -/
def gerverLeftContactBV : ContinuousBVPaths (gerverStageTimes 0) (gerverStageTimes 2) :=
  continuousBVOfContDiffOnIccUnionIcc (fun t ↦ paperGerverContacts t 3)
    (gerverStageTimes_strictMono (show (0 : Fin 6) < 1 by decide)).le
    (gerverStageTimes_strictMono (show (1 : Fin 6) < 2 by decide)).le
    (contDiffOn_paperGerverContact 3 0) (contDiffOn_paperGerverContact 3 1)

/-- `gerverRightContactBV` is the second Gerver contact curve. -/
theorem gerverRightContactBV_apply (t : Set.Icc (gerverStageTimes 3) (gerverStageTimes 5)) :
    gerverRightContactBV.val t = paperGerverContacts t 1 := rfl

/-- `gerverLeftContactBV` is the fourth Gerver contact curve. -/
theorem gerverLeftContactBV_apply (t : Set.Icc (gerverStageTimes 0) (gerverStageTimes 2)) :
    gerverLeftContactBV.val t = paperGerverContacts t 3 := rfl

/-! ### Stage derivatives of the two inner contact curves -/

/-- The velocity components are the frame coordinates of the derivative of the direct path. -/
theorem deriv_paperGerverPath_eq_smul_add_smul {t a b : ℝ}
    (h : paperGerverVelocityComponents t = (a, b)) :
    deriv paperGerverPath t =
      a • normalVector (t : Real.Angle) + b • tangentVector (t : Real.Angle) := by
  have hframe := inner_normalVector_smul_add_inner_tangentVector_smul
    (deriv paperGerverPath t) (t : Real.Angle)
  rw [paperGerverVelocityComponents, Prod.mk.injEq] at h
  rw [h.1, h.2] at hframe
  exact hframe.symm

/-- On a stage where the direct path has velocity components `(α, β)`, the second contact
curve `B = x + α v` has derivative `(β + α') v`: the frame derivative `v' = -u` cancels the
normal component `α u` of `x'`, leaving the tangential component `β v` and the derivative of
the coefficient. -/
theorem hasDerivWithinAt_paperGerverContacts_one {i : Fin 5} {t c α' : ℝ} {α β : ℝ → ℝ}
    (ht : t ∈ gerverStageIntervals i) (hα : HasDerivAt α α' t)
    (hαβ : ∀ s ∈ gerverStageIntervals i, paperGerverVelocityComponents s = (α s, β s))
    (hc : β t + α' = c) :
    HasDerivWithinAt (fun s ↦ paperGerverContacts s 1)
      (c • tangentVector (t : Real.Angle)) (gerverStageIntervals i) t := by
  have hx : HasDerivAt paperGerverPath (deriv paperGerverPath t) t :=
    (contDiff_paperGerverPath.differentiable one_ne_zero t).hasDerivAt
  have hd := deriv_paperGerverPath_eq_smul_add_smul (hαβ t ht)
  have hmain : HasDerivAt (fun s ↦ paperGerverPath s + α s • tangentVector (s : Real.Angle))
      (c • tangentVector (t : Real.Angle)) t := by
    have h := hx.add (hα.smul (hasDerivAt_tangentVector t))
    rw [hd] at h
    rw [← hc]
    convert h using 1
    module
  refine hmain.hasDerivWithinAt.congr (fun y hy ↦ ?_) ?_
  · show paperGerverPath y + (paperGerverVelocityComponents y).1 •
      tangentVector (y : Real.Angle) = _
    rw [hαβ y hy]
  · show paperGerverPath t + (paperGerverVelocityComponents t).1 •
      tangentVector (t : Real.Angle) = _
    rw [hαβ t ht]

/-- On a stage where the direct path has velocity components `(α, β)`, the fourth contact
curve `D = x - β u` has derivative `(α - β') u`; see
`hasDerivWithinAt_paperGerverContacts_one` for the shape of the computation. -/
theorem hasDerivWithinAt_paperGerverContacts_three {i : Fin 5} {t c β' : ℝ} {α β : ℝ → ℝ}
    (ht : t ∈ gerverStageIntervals i) (hβ : HasDerivAt β β' t)
    (hαβ : ∀ s ∈ gerverStageIntervals i, paperGerverVelocityComponents s = (α s, β s))
    (hc : α t - β' = c) :
    HasDerivWithinAt (fun s ↦ paperGerverContacts s 3)
      (c • normalVector (t : Real.Angle)) (gerverStageIntervals i) t := by
  have hx : HasDerivAt paperGerverPath (deriv paperGerverPath t) t :=
    (contDiff_paperGerverPath.differentiable one_ne_zero t).hasDerivAt
  have hd := deriv_paperGerverPath_eq_smul_add_smul (hαβ t ht)
  have hmain : HasDerivAt (fun s ↦ paperGerverPath s - β s • normalVector (s : Real.Angle))
      (c • normalVector (t : Real.Angle)) t := by
    have h := hx.sub (hβ.smul (hasDerivAt_normalVector t))
    rw [hd] at h
    rw [← hc]
    convert h using 1
    module
  refine hmain.hasDerivWithinAt.congr (fun y hy ↦ ?_) ?_
  · show paperGerverPath y - (paperGerverVelocityComponents y).2 •
      normalVector (y : Real.Angle) = _
    rw [hαβ y hy]
  · show paperGerverPath t - (paperGerverVelocityComponents t).2 •
      normalVector (t : Real.Angle) = _
    rw [hαβ t ht]

/-- On each of the last two stages the second contact curve moves strictly backwards along
the tangent direction: its one-sided derivative is a negative multiple of `v_t`.  On the
fourth stage the tangential speed is `d₁ - 1 - t/2`, negative because `t ≥ π/2 - θ > 4/5` and
`d₁ ≤ 33/25`; on the fifth it is the exact constant `-1/2`. -/
theorem hasDerivWithinAt_paperGerverContacts_one_neg_smul {i : Fin 5} (hi : i = 3 ∨ i = 4)
    {t : ℝ} (ht : t ∈ gerverStageIntervals i) :
    ∃ c : ℝ, c < 0 ∧
      HasDerivWithinAt (fun s ↦ paperGerverContacts s 1)
        (c • tangentVector (t : Real.Angle)) (gerverStageIntervals i) t := by
  rcases hi with rfl | rfl
  · have hbranch : ∀ s ∈ gerverStageIntervals 3, paperGerverVelocityComponents s =
        ((1 / 4 : ℝ) * s * s - GerverSofa.PartB.params.d1 * s -
            GerverSofa.PartB.params.d2 - 1 / 2,
          2 * GerverSofa.PartB.params.d1 - 1 - s) := by
      intro s hs
      rw [paperGerverContactData_properties.2.2.2 3 s hs]
      rfl
    have hα : HasDerivAt (fun s : ℝ ↦ (1 / 4 : ℝ) * s * s -
        GerverSofa.PartB.params.d1 * s - GerverSofa.PartB.params.d2 - 1 / 2)
        (t / 2 - GerverSofa.PartB.params.d1) t := by
      have h := ((((hasDerivAt_id' t).const_mul (1 / 4 : ℝ)).mul (hasDerivAt_id' t)).sub
        ((hasDerivAt_id' t).const_mul GerverSofa.PartB.params.d1)).sub_const
          GerverSofa.PartB.params.d2 |>.sub_const (1 / 2 : ℝ)
      convert h using 1
      ring
    refine ⟨GerverSofa.PartB.params.d1 - 1 - t / 2, ?_,
      hasDerivWithinAt_paperGerverContacts_one ht hα hbranch (by ring)⟩
    rw [gerverStageIntervals_three] at ht
    have hrefl : gerverStageTimes 3 = Real.pi / 2 - gerverStageTimes 2 := rfl
    linarith [gerverDirectBox_d1_upper_bound GerverSofa.PartB.params_mem,
      gerverStageTimes_two_le_seven_div_ten, ht.1, Real.pi_gt_three]
  · have hbranch : ∀ s ∈ gerverStageIntervals 4, paperGerverVelocityComponents s =
        (1 - 2 * GerverSofa.PartB.params.e1 * Real.sin s +
            2 * GerverSofa.PartB.params.e2 * Real.cos s,
          2 * GerverSofa.PartB.params.e1 * Real.cos s +
            2 * GerverSofa.PartB.params.e2 * Real.sin s - 1 / 2) := by
      intro s hs
      rw [paperGerverContactData_properties.2.2.2 4 s hs]
      rfl
    have hα : HasDerivAt (fun s : ℝ ↦ 1 - 2 * GerverSofa.PartB.params.e1 * Real.sin s +
        2 * GerverSofa.PartB.params.e2 * Real.cos s)
        (-(2 * GerverSofa.PartB.params.e1 * Real.cos t) -
          2 * GerverSofa.PartB.params.e2 * Real.sin t) t := by
      have h := ((hasDerivAt_const t (1 : ℝ)).sub
        ((Real.hasDerivAt_sin t).const_mul (2 * GerverSofa.PartB.params.e1))).add
        ((Real.hasDerivAt_cos t).const_mul (2 * GerverSofa.PartB.params.e2))
      convert h using 1
      ring
    exact ⟨-(1 / 2), by norm_num,
      hasDerivWithinAt_paperGerverContacts_one ht hα hbranch (by ring)⟩

/-- On each of the first two stages the fourth contact curve moves strictly forwards along
the normal direction: its one-sided derivative is a positive multiple of `u_t`.  On the first
stage the normal speed is the exact constant `1/2`; on the second it is `1 + b₁ - t/2`,
positive because `t ≤ θ ≤ 7/10` and `b₁ ≥ -53/100`. -/
theorem hasDerivWithinAt_paperGerverContacts_three_pos_smul {i : Fin 5} (hi : i = 0 ∨ i = 1)
    {t : ℝ} (ht : t ∈ gerverStageIntervals i) :
    ∃ c : ℝ, 0 < c ∧
      HasDerivWithinAt (fun s ↦ paperGerverContacts s 3)
        (c • normalVector (t : Real.Angle)) (gerverStageIntervals i) t := by
  rcases hi with rfl | rfl
  · have hbranch : ∀ s ∈ gerverStageIntervals 0, paperGerverVelocityComponents s =
        (-2 * GerverSofa.PartB.params.a1 * Real.sin s +
            2 * GerverSofa.PartB.params.a2 * Real.cos s + 1 / 2,
          2 * GerverSofa.PartB.params.a1 * Real.cos s +
            2 * GerverSofa.PartB.params.a2 * Real.sin s - 1) := by
      intro s hs
      rw [paperGerverContactData_properties.2.2.2 0 s hs]
      rfl
    have hβ : HasDerivAt (fun s : ℝ ↦ 2 * GerverSofa.PartB.params.a1 * Real.cos s +
        2 * GerverSofa.PartB.params.a2 * Real.sin s - 1)
        (-(2 * GerverSofa.PartB.params.a1 * Real.sin t) +
          2 * GerverSofa.PartB.params.a2 * Real.cos t) t := by
      have h := (((Real.hasDerivAt_cos t).const_mul (2 * GerverSofa.PartB.params.a1)).add
        ((Real.hasDerivAt_sin t).const_mul (2 * GerverSofa.PartB.params.a2))).sub_const (1 : ℝ)
      convert h using 1
      ring
    exact ⟨1 / 2, by norm_num,
      hasDerivWithinAt_paperGerverContacts_three ht hβ hbranch (by ring)⟩
  · have hbranch : ∀ s ∈ gerverStageIntervals 1, paperGerverVelocityComponents s =
        (1 + 2 * GerverSofa.PartB.params.b1 - s,
          -(1 / 4 : ℝ) * s * s + GerverSofa.PartB.params.b1 * s +
            GerverSofa.PartB.params.b2 + 1 / 2) := by
      intro s hs
      rw [paperGerverContactData_properties.2.2.2 1 s hs]
      rfl
    have hβ : HasDerivAt (fun s : ℝ ↦ -(1 / 4 : ℝ) * s * s +
        GerverSofa.PartB.params.b1 * s + GerverSofa.PartB.params.b2 + 1 / 2)
        (-(t / 2) + GerverSofa.PartB.params.b1) t := by
      have h := ((((hasDerivAt_id' t).const_mul (-(1 / 4) : ℝ)).mul (hasDerivAt_id' t)).add
        ((hasDerivAt_id' t).const_mul GerverSofa.PartB.params.b1)).add_const
          GerverSofa.PartB.params.b2 |>.add_const (1 / 2 : ℝ)
      convert h using 1
      ring
    refine ⟨1 + GerverSofa.PartB.params.b1 - t / 2, ?_,
      hasDerivWithinAt_paperGerverContacts_three ht hβ hbranch (by ring)⟩
    rw [gerverStageIntervals_one] at ht
    linarith [gerverDirectBox_b1_lower_bound GerverSofa.PartB.params_mem,
      gerverStageTimes_two_le_seven_div_ten, ht.2]

/-! ### Frame coordinates of the direct path -/

/-- The derivative of the direct Gerver path in the moving frame. -/
theorem hasDerivAt_paperGerverPath_frame (t : ℝ) :
    HasDerivAt paperGerverPath
      ((paperGerverVelocityComponents t).1 • normalVector (t : Real.Angle) +
        (paperGerverVelocityComponents t).2 • tangentVector (t : Real.Angle)) t := by
  have h := (contDiff_paperGerverPath.differentiable one_ne_zero t).hasDerivAt
  rwa [deriv_paperGerverPath_eq_smul_add_smul rfl] at h

/-- The angular derivative of the normal frame coordinate of the Gerver path is the tangent
coordinate of the second contact curve: with `B = x + α v` the frame derivative `u' = v`
contributes `x ⋅ v` and the normal component of `x'` contributes `α`. -/
theorem hasDerivAt_inner_paperGerverPath_normalVector (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ inner ℝ (paperGerverPath s) (normalVector (s : Real.Angle)))
      (inner ℝ (paperGerverContacts t 1) (tangentVector (t : Real.Angle))) t := by
  have h := (hasDerivAt_paperGerverPath_frame t).inner ℝ (hasDerivAt_normalVector t)
  convert h using 1
  show inner ℝ (paperGerverPath t + (paperGerverVelocityComponents t).1 •
    tangentVector (t : Real.Angle)) (tangentVector (t : Real.Angle)) = _
  rw [inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    real_inner_smul_left, inner_tangentVector_self, inner_normalVector_self,
    inner_tangentVector_normalVector_real, sub_self, Real.sin_zero]
  ring

/-- The angular derivative of the tangent frame coordinate of the Gerver path is minus the
normal coordinate of the fourth contact curve: with `D = x - β u` the frame derivative
`v' = -u` contributes `-x ⋅ u` and the tangent component of `x'` contributes `β`. -/
theorem hasDerivAt_inner_paperGerverPath_tangentVector (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ inner ℝ (paperGerverPath s) (tangentVector (s : Real.Angle)))
      (-inner ℝ (paperGerverContacts t 3) (normalVector (t : Real.Angle))) t := by
  have h := (hasDerivAt_paperGerverPath_frame t).inner ℝ (hasDerivAt_tangentVector t)
  convert h using 1
  show -inner ℝ (paperGerverPath t - (paperGerverVelocityComponents t).2 •
    normalVector (t : Real.Angle)) (normalVector (t : Real.Angle)) = _
  rw [inner_sub_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    real_inner_smul_left, inner_neg_right, inner_normalVector_self, inner_tangentVector_self,
    inner_normalVector_tangentVector]
  ring

/-! ### Stagewise monotonicity of the inner contact curves against a fixed direction -/

/-- Against the tangent direction at a later angle `c`, the fourth Gerver contact curve is
strictly antitone on each of its first two stages: its stage speed is a positive multiple of
`u_s`, whose `v_c` coordinate is `sin (s - c) < 0`. -/
theorem strictAntiOn_inner_paperGerverContacts_three {i : Fin 5} (hi : i = 0 ∨ i = 1) {c : ℝ}
    (hlt : ∀ s ∈ gerverStageIntervals i, s < c)
    (hwide : ∀ s ∈ gerverStageIntervals i, c - Real.pi < s) :
    StrictAntiOn (fun s ↦ inner ℝ (paperGerverContacts s 3) (tangentVector (c : Real.Angle)))
      (gerverStageIntervals i) := by
  rw [show gerverStageIntervals i =
    Set.Icc (gerverStageTimes i.castSucc) (gerverStageTimes i.succ) from rfl] at hlt hwide ⊢
  have hspeed : ∀ s ∈ interior (Set.Icc (gerverStageTimes i.castSucc)
      (gerverStageTimes i.succ)), ∃ cs : ℝ, 0 < cs ∧
      derivWithin (fun r ↦ paperGerverContacts r 3)
          (interior (Set.Icc (gerverStageTimes i.castSucc) (gerverStageTimes i.succ))) s =
        cs • normalVector (s : Real.Angle) ∧
      HasDerivWithinAt (fun r ↦ paperGerverContacts r 3) (cs • normalVector (s : Real.Angle))
        (interior (Set.Icc (gerverStageTimes i.castSucc) (gerverStageTimes i.succ))) s := by
    intro s hs
    obtain ⟨cs, hcs, hder⟩ :=
      hasDerivWithinAt_paperGerverContacts_three_pos_smul hi (interior_subset hs)
    exact ⟨cs, hcs, (hder.mono interior_subset).derivWithin
      (isOpen_interior.uniqueDiffWithinAt hs), hder.mono interior_subset⟩
  refine strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc _ _)
    ((continuous_paperGerverContact 3).continuousOn.inner continuousOn_const)
    (f' := fun s ↦ inner ℝ (derivWithin (fun r ↦ paperGerverContacts r 3)
      (interior (Set.Icc (gerverStageTimes i.castSucc) (gerverStageTimes i.succ))) s)
      (tangentVector (c : Real.Angle))) ?_ ?_
  · intro s hs
    obtain ⟨cs, -, hu, hder⟩ := hspeed s hs
    rw [hu]
    simpa using
      hder.inner ℝ (hasDerivWithinAt_const s _ (tangentVector (c : Real.Angle)))
  · intro s hs
    obtain ⟨cs, hcs, hu, -⟩ := hspeed s hs
    rw [hu, real_inner_smul_left,
      real_inner_comm (tangentVector (c : Real.Angle)) (normalVector (s : Real.Angle)),
      inner_tangentVector_normalVector_real]
    exact mul_neg_of_pos_of_neg hcs (Real.sin_neg_of_neg_of_neg_pi_lt
      (by linarith only [hlt s (interior_subset hs)])
      (by linarith only [hwide s (interior_subset hs)]))

/-- Against the normal direction at an earlier angle `c`, the second Gerver contact curve is
strictly monotone on each of its last two stages: its stage speed is a negative multiple of
`v_s`, whose `u_c` coordinate is `sin (c - s) < 0`. -/
theorem strictMonoOn_inner_paperGerverContacts_one {i : Fin 5} (hi : i = 3 ∨ i = 4) {c : ℝ}
    (hlt : ∀ s ∈ gerverStageIntervals i, c < s)
    (hwide : ∀ s ∈ gerverStageIntervals i, s < c + Real.pi) :
    StrictMonoOn (fun s ↦ inner ℝ (paperGerverContacts s 1) (normalVector (c : Real.Angle)))
      (gerverStageIntervals i) := by
  rw [show gerverStageIntervals i =
    Set.Icc (gerverStageTimes i.castSucc) (gerverStageTimes i.succ) from rfl] at hlt hwide ⊢
  have hspeed : ∀ s ∈ interior (Set.Icc (gerverStageTimes i.castSucc)
      (gerverStageTimes i.succ)), ∃ cs : ℝ, cs < 0 ∧
      derivWithin (fun r ↦ paperGerverContacts r 1)
          (interior (Set.Icc (gerverStageTimes i.castSucc) (gerverStageTimes i.succ))) s =
        cs • tangentVector (s : Real.Angle) ∧
      HasDerivWithinAt (fun r ↦ paperGerverContacts r 1) (cs • tangentVector (s : Real.Angle))
        (interior (Set.Icc (gerverStageTimes i.castSucc) (gerverStageTimes i.succ))) s := by
    intro s hs
    obtain ⟨cs, hcs, hder⟩ :=
      hasDerivWithinAt_paperGerverContacts_one_neg_smul hi (interior_subset hs)
    exact ⟨cs, hcs, (hder.mono interior_subset).derivWithin
      (isOpen_interior.uniqueDiffWithinAt hs), hder.mono interior_subset⟩
  refine strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _)
    ((continuous_paperGerverContact 1).continuousOn.inner continuousOn_const)
    (f' := fun s ↦ inner ℝ (derivWithin (fun r ↦ paperGerverContacts r 1)
      (interior (Set.Icc (gerverStageTimes i.castSucc) (gerverStageTimes i.succ))) s)
      (normalVector (c : Real.Angle))) ?_ ?_
  · intro s hs
    obtain ⟨cs, -, hu, hder⟩ := hspeed s hs
    rw [hu]
    simpa using
      hder.inner ℝ (hasDerivWithinAt_const s _ (normalVector (c : Real.Angle)))
  · intro s hs
    obtain ⟨cs, hcs, hu, -⟩ := hspeed s hs
    rw [hu, real_inner_smul_left, inner_tangentVector_normalVector_real]
    exact mul_pos_of_neg_of_neg hcs (Real.sin_neg_of_neg_of_neg_pi_lt
      (by linarith only [hlt s (interior_subset hs)])
      (by linarith only [hwide s (interior_subset hs)]))

end MovingSofa
