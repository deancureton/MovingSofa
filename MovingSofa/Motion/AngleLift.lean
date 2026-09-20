import MovingSofa.Motion.Rotation
import MovingSofa.ForMathlib.Topology.Angle

noncomputable section

open scoped unitInterval

namespace MovingSofa

/-- An identity-starting continuous rigid motion has a normalized continuous real angle lift. -/
theorem exists_continuous_motion_angle_lift (m : I → Point ≃ᵃⁱ[ℝ] Point)
    (hm : Continuous m) (hzero : m 0 = AffineIsometryEquiv.refl ℝ Point) :
    ∃ (α : I → ℝ) (p : I → Point), Continuous α ∧ Continuous p ∧
      α 0 = 0 ∧ p 0 = 0 ∧ ∀ t x, m t x = rotationMap (α t : Real.Angle) x + p t := by
  let e : Point := !₂[1, 0]
  have he : e ≠ 0 := by
    intro h
    have := congrArg (fun p : Point ↦ p 0) h
    norm_num [e] at this
  let θ : I → Real.Angle := fun t ↦ EuclideanGeometry.o.oangle e
    ((m t).linearIsometryEquiv e)
  have hθ : Continuous θ := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hne : (m t).linearIsometryEquiv e ≠ 0 := by
      exact (m t).linearIsometryEquiv.map_ne_zero_iff.mpr he
    have ha : ContinuousAt (fun z : Point × Point ↦ EuclideanGeometry.o.oangle z.1 z.2)
        (e, (m t).linearIsometryEquiv e) :=
      EuclideanGeometry.o.continuousAt_oangle he hne
    have hp : ContinuousAt (fun u : I ↦ (e, (m u).linearIsometryEquiv e)) t :=
      continuousAt_const.prodMk (continuous_motion_linear_apply m hm e).continuousAt
    exact ContinuousAt.comp (f := fun u : I ↦ (e, (m u).linearIsometryEquiv e))
      (x := t) ha hp
  have hθ0 : θ 0 = 0 := by
    have h0 : (m 0).linearIsometryEquiv e = e := by rw [hzero]; rfl
    simp [θ, h0]
  have hrot (t : I) : (m t).linearIsometryEquiv = EuclideanGeometry.o.rotation (θ t) := by
    obtain ⟨u, hu⟩ := EuclideanGeometry.o.exists_linearIsometryEquiv_eq_of_det_pos
      (motion_linear_det_pos m hm hzero t)
    have ht : θ t = u := by
      dsimp [θ]
      rw [hu, EuclideanGeometry.o.oangle_rotation_self_right he]
    rw [ht, hu]
  obtain ⟨α, hα, hα0, hαθ⟩ := Real.Angle.exists_continuous_lift_zero θ hθ hθ0
  have hp : Continuous (fun t ↦ m t (0 : Point)) := by
    have hmc : Continuous (fun t ↦ (m t).toAffineIsometry.toContinuousAffineMap) :=
      continuous_induced_dom.comp hm
    exact hmc.eval_const 0
  refine ⟨α, fun t ↦ m t 0, hα, hp, hα0, ?_, ?_⟩
  · change m 0 0 = 0
    rw [hzero]
    rfl
  · intro t x
    have hx := (m t).map_vadd (0 : Point) x
    change m t (x + 0) = (m t).linearIsometryEquiv x + m t 0 at hx
    simpa only [add_zero, hrot t, hαθ t, rotationMap] using hx

end MovingSofa
