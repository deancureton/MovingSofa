import MovingSofa.Gerver.Contacts

/-!
# The Gerver niche roof

The upper boundary of the paper's literal Gerver niche is a three-piece graph over the
rotation interval: the fourth contact curve up to the second stage time, the direct path run
*backwards* through the affine reversal `gerverRoofReverseTime` on the middle stage, and the
second contact curve from the third stage time on.  `gerverRoofCurve` is that graph as a
function of an unrestricted real parameter and `gerverNicheRoof` its restriction to the
rotation interval; `gerverRoofCurve_eq` relates the two.
-/

noncomputable section

namespace MovingSofa

/-- The affine reversal of the middle roof stage: it maps `gerverStageTimes 2` to
`gerverStageTimes 4` and `gerverStageTimes 3` to `gerverStageTimes 1`, so it reparametrizes
the central part of the direct path backwards. -/
def gerverRoofReverseTime (s : ℝ) : ℝ :=
  gerverStageTimes 4 - (gerverStageTimes 4 - gerverStageTimes 1) /
    (gerverStageTimes 3 - gerverStageTimes 2) * (s - gerverStageTimes 2)

/-- The Gerver niche roof as a curve of an unrestricted real parameter.  On the rotation
interval it agrees with `gerverNicheRoof` (`gerverRoofCurve_eq`); the unrestricted form is
what the intermediate value theorem and `continuous_if_le` consume. -/
def gerverRoofCurve (s : ℝ) : Point :=
  if s ≤ gerverStageTimes 2 then paperGerverContacts s 3
  else if s ≤ gerverStageTimes 3 then paperGerverPath (gerverRoofReverseTime s)
  else paperGerverContacts s 1

def gerverNicheRoof (s : Set.Icc (0 : ℝ) (Real.pi / 2)) : Point :=
  if s.val ≤ gerverStageTimes 2 then paperGerverContacts s.val 3
  else if s.val ≤ gerverStageTimes 3 then paperGerverPath (gerverRoofReverseTime s.val)
  else paperGerverContacts s.val 1

end MovingSofa
