import Mathlib.Analysis.Convex.Body

/-- Translation of a convex body by a vector. -/
def ConvexBody.translate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : ConvexBody E) (v : E) : ConvexBody E where
  carrier := (fun p ↦ p + v) '' (K : Set E)
  convex' := by simpa only [add_comm] using K.convex.translate v
  isCompact' := K.isCompact.image (continuous_id.add continuous_const)
  nonempty' := K.nonempty.image _
