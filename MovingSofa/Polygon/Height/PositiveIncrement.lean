import MovingSofa.Polygon.Height.PositiveIncrement.Contacts

noncomputable section

namespace MovingSofa

theorem polygonCap_positive_height_increment {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (t : angleDomain Θ)
    (ht : 0 < surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ K' : PolygonCapTranslateSpace Θ,
        K'.val = polygonHeightCap (raisedPolygonSupport K t ε) := by
  by_cases htendpoint : t.val ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)
  · exact polygonCap_positive_height_increment_of_endpoint K t htendpoint ht
  · exact polygonCap_positive_height_increment_of_not_endpoint K t htendpoint

end MovingSofa
