import MovingSofa.Cap.Tail.Bodies

noncomputable section

namespace MovingSofa

/-- The canonical tail sets give an admissible cap-tail triple with exactly these carriers. -/
theorem exists_canonicalCapTail (K : SpecialCapSpace) :
    ∃ T : CapTailSpace, T.cap = K ∧
      (T.rightBody : Set Point) = (canonicalTailSets K).1 ∧
      (T.leftBody : Set Point) = (canonicalTailSets K).2 := by
  obtain ⟨hBne, hBcp, hBcv, hBsub, hDne, hDcp, hDcv, hDsub, hBbd, hBeq, -, -,
    hDbd, hDeq, -, -⟩ := canonicalTailSets_properties K
  exact ⟨{ cap := K
           rightBody := ⟨(canonicalTailSets K).1, hBcv, hBcp, hBne⟩
           leftBody := ⟨(canonicalTailSets K).2, hDcv, hDcp, hDne⟩
           right_subset := hBsub
           left_subset := hDsub
           right_bound := hBbd
           right_eq := hBeq
           left_bound := hDbd
           left_eq := hDeq }, rfl, rfl, rfl⟩

end MovingSofa
