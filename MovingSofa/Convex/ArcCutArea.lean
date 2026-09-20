import MovingSofa.Curve.Jordan.SubarcArea
import MovingSofa.Convex.CurveCut

noncomputable section

namespace MovingSofa

open Set

/-- A supporting chord of a convex-body frontier cuts off a rectifiable oriented arc, and the
closed signed area is the sum of the arc area and the oppositely oriented chord area. -/
theorem exists_rectifiableOrientedArc_of_cut_with_area
    (K : ConvexBody Point) {t c d α β : ℝ} {P Q : Point} {U : Set Point}
    {x : ContinuousBVPaths α β}
    (hαβ : α < β)
    (hx : IsOrientedJordanParametrization hαβ.le (frontier (K : Set Point)) true x.val)
    (hPQ : P ≠ Q) (hbase : x.val ⟨α, le_rfl, hαβ.le⟩ ∉ segment ℝ P Q)
    (hfrontier : frontier (K : Set Point) = U ∪ segment ℝ P Q)
    (hinter : U ∩ segment ℝ P Q = {P, Q})
    (hPt : inner ℝ P (normalVector (t : Real.Angle)) = c)
    (hQt : inner ℝ Q (normalVector (t : Real.Angle)) = c)
    (hterminal : exposedEdge K (t + Real.pi) = segment ℝ Q P)
    (hd : 0 < d) (hdir : Q - P = d • tangentVector (t : Real.Angle)) :
    ∃ A : RectifiableOrientedArc,
      A.val.carrier = U ∧
      A.val.startPoint = P ∧ A.val.endPoint = Q ∧
      curveAreaFunctional x = jordanArcArea A + segmentArea Q P := by
  let θ : Real.Angle := (t + Real.pi : ℝ)
  have hhalf : frontier (K : Set Point) ⊆ normalHalfPlane θ (-c) false false := by
    intro z hz
    have hzK : z ∈ K := K.isClosed.frontier_subset hz
    have hzle := inner_le_supportValue K hzK θ
    have hPterm : P ∈ exposedEdge K θ := by
      rw [show exposedEdge K θ = segment ℝ Q P by
        simpa only [θ, Real.Angle.coe_add] using hterminal]
      exact right_mem_segment ℝ Q P
    have hsupp : supportValue K θ = -c := by
      have h := hPterm.2
      change inner ℝ P (normalVector θ) = supportValue K θ at h
      change inner ℝ P (normalVector (((t + Real.pi : ℝ) : Real.Angle))) = _ at h
      rw [normalVector_add_pi, inner_neg_right, hPt] at h
      linarith
    change inner ℝ z (normalVector θ) ≤ -c
    rwa [hsupp] at hzle
  have hQline : Q ∈ normalLine θ (-c) := by
    change inner ℝ Q (normalVector θ) = -c
    change inner ℝ Q (normalVector (((t + Real.pi : ℝ) : Real.Angle))) = -c
    rw [normalVector_add_pi, inner_neg_right, hQt]
  have hdir' : P = Q + d • tangentVector θ := by
    have htangent : tangentVector θ = -tangentVector (t : Real.Angle) := by
      ext i
      fin_cases i <;> simp [θ, tangentVector, frame]
    rw [htangent]
    calc
      P = Q - (Q - P) := by module
      _ = Q - d • tangentVector (t : Real.Angle) := by rw [hdir]
      _ = Q + d • -tangentVector (t : Real.Angle) := by module
  exact exists_rectifiableOrientedArc_of_supportingChord_with_area
    hαβ hx P Q hPQ
    hbase hfrontier hinter θ (-c) hhalf hQline d hd hdir'

end MovingSofa
