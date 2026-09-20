import GerverSofa.ExactReplay

/-!
# Part B exact product-cell arithmetic

This module is deliberately independent of the noncomputable Part A root.
It contains only exact rational interval data, so all 64 diagnostic and
production rows can be kernel-reduced without rebuilding semantic layers.
-/

namespace GerverSofa
namespace PartB

open RatInterval

/-- Exact target `0.171` used by the continuum theorem. -/
def targetQ : ℚ := 171 / 1000

/-- The 64 closed mesh cells determined by the 65 nodes `iπ/128`. -/
abbrev Cell := Fin 64

/-- Exact rational mesh coefficient. -/
def nodeCoeff (i : Nat) : ℚ := (i : ℚ) / 128

/-- Hull of two rational intervals. -/
def intervalHull (a b : RatInterval) : RatInterval :=
  ⟨min a.lo b.lo, max a.hi b.hi⟩

/-- Componentwise hull of two planar interval boxes. -/
def pointHull (a b : RatInterval × RatInterval) : RatInterval × RatInterval :=
  (intervalHull a.1 b.1, intervalHull a.2 b.2)

/-- Exact interval enclosure of one physical time cell. -/
def cellTimeInterval (i : Cell) : RatInterval :=
  intervalHull
    (ExactReplay.scale (nodeCoeff i.1) ExactReplay.piI)
    (ExactReplay.scale (nodeCoeff (i.1 + 1)) ExactReplay.piI)

/-- Exact interval evaluation of one path phase on one complete mesh cell. -/
def cellPieceInterval (j : Nat) (i : Cell) : RatInterval × RatInterval :=
  let t := cellTimeInterval i
  let k11 := ExactReplay.getI ExactReplay.fullInputBox 0
  let k12 := ExactReplay.getI ExactReplay.fullInputBox 1
  let k21 := ExactReplay.getI ExactReplay.fullInputBox 2
  let k22 := ExactReplay.getI ExactReplay.fullInputBox 3
  let k31 := ExactReplay.getI ExactReplay.fullInputBox 4
  let k32 := ExactReplay.getI ExactReplay.fullInputBox 5
  let k41 := ExactReplay.getI ExactReplay.fullInputBox 6
  let k42 := ExactReplay.getI ExactReplay.fullInputBox 7
  let k51 := ExactReplay.getI ExactReplay.fullInputBox 8
  let k52 := ExactReplay.getI ExactReplay.fullInputBox 9
  let a1 := ExactReplay.getI ExactReplay.fullInputBox 10
  let a2 := ExactReplay.getI ExactReplay.fullInputBox 11
  let b1 := ExactReplay.getI ExactReplay.fullInputBox 12
  let b2 := ExactReplay.getI ExactReplay.fullInputBox 13
  let c1 := ExactReplay.getI ExactReplay.fullInputBox 14
  let c2 := ExactReplay.getI ExactReplay.fullInputBox 15
  let d1 := ExactReplay.getI ExactReplay.fullInputBox 16
  let d2 := ExactReplay.getI ExactReplay.fullInputBox 17
  let e1 := ExactReplay.getI ExactReplay.fullInputBox 18
  let e2 := ExactReplay.getI ExactReplay.fullInputBox 19
  let one := ExactReplay.oneI
  let half := RatInterval.point (1 / 2)
  let quarter := RatInterval.point (1 / 4)
  let ct := ExactReplay.cosineInterval t
  let st := ExactReplay.sineInterval t
  let data : RatInterval × RatInterval × RatInterval × RatInterval :=
    if j = 1 then
      (RatInterval.sub
          (RatInterval.add (RatInterval.mul a1 ct) (RatInterval.mul a2 st)) one,
       RatInterval.sub
          (RatInterval.add (RatInterval.mul (RatInterval.neg a2) ct)
            (RatInterval.mul a1 st)) half,
       k11, k12)
    else if j = 2 then
      (RatInterval.add
          (RatInterval.add
            (RatInterval.mul (RatInterval.neg quarter) (RatInterval.mul t t))
            (RatInterval.mul b1 t)) b2,
       RatInterval.sub
          (RatInterval.sub (RatInterval.mul half t) b1) one,
       k21, k22)
    else if j = 3 then
      (RatInterval.sub c1 t, RatInterval.add c2 t, k31, k32)
    else if j = 4 then
      (RatInterval.sub
          (RatInterval.add (RatInterval.mul (RatInterval.neg half) t) d1) one,
       RatInterval.add
          (RatInterval.add
            (RatInterval.mul (RatInterval.neg quarter) (RatInterval.mul t t))
            (RatInterval.mul d1 t)) d2,
       k41, k42)
    else
      (RatInterval.sub
          (RatInterval.add (RatInterval.mul e1 ct) (RatInterval.mul e2 st)) half,
       RatInterval.sub
          (RatInterval.add (RatInterval.mul (RatInterval.neg e2) ct)
            (RatInterval.mul e1 st)) one,
       k51, k52)
  let r1 := RatInterval.sub (RatInterval.mul ct data.1)
      (RatInterval.mul st data.2.1)
  let r2 := RatInterval.add (RatInterval.mul st data.1)
      (RatInterval.mul ct data.2.1)
  (RatInterval.add r1 data.2.2.1, RatInterval.add r2 data.2.2.2)

/-- The path enclosure for a cell.  Four cells contain a switching angle and
therefore take the hull of the two adjacent analytic phases. -/
def cellPathInterval (i : Cell) : RatInterval × RatInterval :=
  if i.1 = 0 then cellPieceInterval 1 i
  else if i.1 = 1 then pointHull (cellPieceInterval 1 i) (cellPieceInterval 2 i)
  else if i.1 ≤ 26 then cellPieceInterval 2 i
  else if i.1 = 27 then pointHull (cellPieceInterval 2 i) (cellPieceInterval 3 i)
  else if i.1 ≤ 35 then cellPieceInterval 3 i
  else if i.1 = 36 then pointHull (cellPieceInterval 3 i) (cellPieceInterval 4 i)
  else if i.1 ≤ 61 then cellPieceInterval 4 i
  else if i.1 = 62 then pointHull (cellPieceInterval 4 i) (cellPieceInterval 5 i)
  else cellPieceInterval 5 i

/-- Exact interval image of `Gu` on one product cell. -/
def guCellInterval (i j : Cell) : RatInterval :=
  let xi := cellPathInterval i
  let xj := cellPathInterval j
  let c := ExactReplay.cosineInterval (cellTimeInterval i)
  let s := ExactReplay.sineInterval (cellTimeInterval i)
  let dx := RatInterval.sub xi.1 xj.1
  let dy := RatInterval.sub xi.2 xj.2
  RatInterval.add
    (RatInterval.add ExactReplay.oneI (RatInterval.mul dx c))
    (RatInterval.mul dy s)

/-- Exact interval image of `Gv` on one product cell. -/
def gvCellInterval (i j : Cell) : RatInterval :=
  let xi := cellPathInterval i
  let xj := cellPathInterval j
  let c := ExactReplay.cosineInterval (cellTimeInterval i)
  let s := ExactReplay.sineInterval (cellTimeInterval i)
  let dx := RatInterval.sub xi.1 xj.1
  let dy := RatInterval.sub xi.2 xj.2
  RatInterval.add
    (RatInterval.add ExactReplay.oneI
      (RatInterval.mul dx (RatInterval.neg s)))
    (RatInterval.mul dy c)

end PartB
end GerverSofa
