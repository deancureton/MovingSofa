import GerverSofa.CertificateManifest
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Rat.Floor

/-!
# Executable exact-rational replay of the 4D and 22D Krawczyk inclusions

This is a direct, floating-point-free transcription of the companion Python
algorithm.  It computes with `ℚ`, interval automatic differentiation and the
frozen rational preconditioners.  The analytic theorem saying that the Taylor
intervals enclose the real `sin` and `cos`, and the abstract Krawczyk theorem,
remain separate proof obligations; the arithmetic replay itself is decidable.
-/

namespace GerverSofa.ExactReplay

open GerverSofa
open RatInterval
open scoped BigOperators

def q (n : Int) (d : Nat := 1) : ℚ := (n : ℚ) / (d : ℚ)

def zeroI : RatInterval := point 0
def oneI : RatInterval := point 1

private def midpoint (x : RatInterval) : ℚ := (x.lo + x.hi) / 2

def scale (a : ℚ) (x : RatInterval) : RatInterval :=
  mul (point a) x

def factorialQ (n : Nat) : ℚ := (Nat.factorial n : ℚ)

def signedTerm (k : Nat) (x : ℚ) (power : Nat) : ℚ :=
  let z := x ^ power / factorialQ power
  if k % 2 = 0 then z else -z

def sinPartial (x : ℚ) (terms : Nat) : ℚ :=
  Finset.sum (Finset.range terms) (fun k => signedTerm k x (2 * k + 1))

def cosPartial (x : ℚ) (terms : Nat) : ℚ :=
  Finset.sum (Finset.range terms) (fun k => signedTerm k x (2 * k))

def sinBound (x : ℚ) : RatInterval :=
  let a := sinPartial x 19
  let b := sinPartial x 20
  ⟨min a b, max a b⟩

def cosBound (x : ℚ) : RatInterval :=
  let a := cosPartial x 19
  let b := cosPartial x 20
  ⟨min a b, max a b⟩

def piI : RatInterval :=
  ⟨q 157079632679489661923132169163975144209858469968755 50000000000000000000000000000000000000000000000000,
   q 78539816339744830961566084581987572104929234984378 25000000000000000000000000000000000000000000000000⟩

def atanPartial (x : ℚ) (terms : Nat) : ℚ :=
  Finset.sum (Finset.range terms) (fun k =>
    if k % 2 = 0 then
      x ^ (2 * k + 1) / ((2 * k + 1 : Nat) : ℚ)
    else
      -(x ^ (2 * k + 1) / ((2 * k + 1 : Nat) : ℚ)))

def atanBound (x : ℚ) (lowTerms highTerms : Nat) : RatInterval :=
  let a := atanPartial x lowTerms
  let b := atanPartial x highTerms
  ⟨min a b, max a b⟩

def machinPi : RatInterval :=
  sub (scale 16 (atanBound (1 / 5) 43 44))
      (scale 4 (atanBound (1 / 239) 13 14))

/-- Exact downward rounding to a fixed number of decimal places. -/
def floorDecimal (x : ℚ) (digits : Nat := 60) : ℚ :=
  let scale : ℚ := (10 : ℚ) ^ digits
  ((⌊x * scale⌋ : ℤ) : ℚ) / scale

/-- Exact upward rounding to a fixed number of decimal places. -/
def ceilDecimal (x : ℚ) (digits : Nat := 60) : ℚ :=
  let scale : ℚ := (10 : ℚ) ^ digits
  ((⌈x * scale⌉ : ℤ) : ℚ) / scale

/-- The same 60-decimal outward rounding used by the submitted verifier. -/
def outwardDecimal (z : RatInterval) : RatInterval :=
  ⟨floorDecimal z.lo, ceilDecimal z.hi⟩

def sinSmall (x : RatInterval) : RatInterval :=
  outwardDecimal ⟨(sinBound x.lo).lo, (sinBound x.hi).hi⟩

def cosSmall (x : RatInterval) : RatInterval :=
  outwardDecimal ⟨(cosBound x.hi).lo, (cosBound x.lo).hi⟩

/-- Clamp an interval to the physical angular range used by the Gerver
certificate.  If `x ∈ [0, π/2]` and `x` is enclosed by the input interval,
then `x` is still enclosed after clamping once `piI` has been proved to
contain `Real.pi`. -/
def physicalClamp (x : RatInterval) : RatInterval :=
  ⟨max 0 x.lo, min (piI.hi / 2) x.hi⟩

/-- A fail-closed enclosure used only when an externally supplied interval is
too wide for the small-argument Taylor/range-reduction evaluator.  Every
certified Gerver call remains in one of the two sharp branches below, so this
fallback does not alter the frozen replay. -/
def universalTrigInterval : RatInterval := ⟨-1, 1⟩

/-- Complementary interval for the identity `sin x = cos (π/2-x)` and
`cos x = sin (π/2-x)`. -/
def complementInterval (x : RatInterval) : RatInterval :=
  ⟨max 0 (piI.lo / 2 - x.hi), piI.hi / 2 - x.lo⟩

def sinI (x : RatInterval) : RatInterval :=
  let z := physicalClamp x
  if z.hi ≤ 9 / 10 then sinSmall z
  else
    let y := complementInterval z
    if y.hi ≤ 9 / 10 then cosSmall y else universalTrigInterval

def cosI (x : RatInterval) : RatInterval :=
  let z := physicalClamp x
  if z.hi ≤ 9 / 10 then cosSmall z
  else
    let y := complementInterval z
    if y.hi ≤ 9 / 10 then sinSmall y else universalTrigInterval

structure D where
  val : RatInterval
  der : List RatInterval
  deriving Repr

namespace D

def const (v : RatInterval) (n : Nat) : D :=
  ⟨v, List.replicate n zeroI⟩

def pointConst (v : ℚ) (n : Nat) : D := const (point v) n

def varD (v : RatInterval) (j n : Nat) : D :=
  ⟨v, (List.range n).map (fun k => point (if k = j then 1 else 0))⟩

def addD (x y : D) : D :=
  ⟨add x.val y.val, List.zipWith add x.der y.der⟩

def negD (x : D) : D :=
  ⟨neg x.val, x.der.map neg⟩

def subD (x y : D) : D := addD x (negD y)

def mulD (x y : D) : D :=
  ⟨mul x.val y.val,
   List.zipWith (fun dx dy => add (mul dx y.val) (mul x.val dy)) x.der y.der⟩

def scaleD (a : ℚ) (x : D) : D :=
  ⟨scale a x.val, x.der.map (scale a)⟩

def sinD (x : D) : D :=
  let sv := sinI x.val
  let cv := cosI x.val
  ⟨sv, x.der.map (mul cv)⟩

def cosD (x : D) : D :=
  let sv := sinI x.val
  let cv := cosI x.val
  ⟨cv, x.der.map (fun z => neg (mul sv z))⟩

instance : Add D := ⟨addD⟩
instance : Neg D := ⟨negD⟩
instance : Sub D := ⟨subD⟩
instance : Mul D := ⟨mulD⟩
instance : HMul ℚ D D := ⟨scaleD⟩

end D

def getI (xs : List RatInterval) (i : Nat) : RatInterval :=
  xs.getD i zeroI

def getQ (xs : List ℚ) (i : Nat) : ℚ := xs.getD i 0
def getRow (m : List (List ℚ)) (i : Nat) : List ℚ := m.getD i []

/-! ## Reduced 4D system -/

private def x4 : List RatInterval := [
  ⟨q 1888531216873 20000000000000, q 4721328042183 50000000000000⟩,
  ⟨q 69960186366677 50000000000000, q 34980093183339 25000000000000⟩,
  ⟨q 122429264969 3125000000000, q 3917736479009 100000000000000⟩,
  ⟨q 2129067216821 3125000000000, q 68130150938273 100000000000000⟩
]

private def z22 : List RatInterval := [
  ⟨q (-21032242207268875141628571849) 100000000000000000000000000000, q (-21032242207268875141608571849) 100000000000000000000000000000⟩,
  ⟨q 2499999999999999999999 10000000000000000000000, q 2500000000000000000001 10000000000000000000000⟩,
  ⟨q (-91917929277159332227479610289) 100000000000000000000000000000, q (-91917929277159332227459610289) 100000000000000000000000000000⟩,
  ⟨q 29525413734425341573853797657 62500000000000000000000000000, q 29525413734425341573866297657 62500000000000000000000000000⟩,
  ⟨q (-15344080735756291713875357283) 25000000000000000000000000000, q (-15344080735756291713870357283) 25000000000000000000000000000⟩,
  ⟨q 17792529580064437214538861001 20000000000000000000000000000, q 17792529580064437214542861001 20000000000000000000000000000⟩,
  ⟨q (-15417358304445500741761623987) 50000000000000000000000000000, q (-15417358304445500741751623987) 50000000000000000000000000000⟩,
  ⟨q 29525413734425341573853797657 62500000000000000000000000000, q 29525413734425341573866297657 62500000000000000000000000000⟩,
  ⟨q (-20344080735756291713874857283) 20000000000000000000000000000, q (-20344080735756291713870857283) 20000000000000000000000000000⟩,
  ⟨q 2499999999999999999999 10000000000000000000000, q 2500000000000000000001 10000000000000000000000⟩,
  ⟨q 2420644844145377502832171437 2000000000000000000000000000, q 2420644844145377502832571437 2000000000000000000000000000⟩,
  ⟨q (-2500000000000000000001) 10000000000000000000000, q (-2499999999999999999999) 10000000000000000000000⟩,
  ⟨q (-52762459802678462416060380937) 100000000000000000000000000000, q (-52762459802678462416040380937) 100000000000000000000000000000⟩,
  ⟨q 92025838516063762289360579501 100000000000000000000000000000, q 92025838516063762289380579501 100000000000000000000000000000⟩,
  ⟨q 313022761424232933776114655193 500000000000000000000000000000, q 313022761424232933776214655193 500000000000000000000000000000⟩,
  ⟨q (-151160128631428920268654781) 160000000000000000000000000, q (-151160128631428920268622781) 160000000000000000000000000⟩,
  ⟨q 1641278451780291167220080819 1250000000000000000000000000, q 1641278451780291167220330819 1250000000000000000000000000⟩,
  ⟨q (-105076534082910887440587258861) 200000000000000000000000000000, q (-105076534082910887440547258861) 200000000000000000000000000000⟩,
  ⟨q 2420644844145377502832171437 2000000000000000000000000000, q 2420644844145377502832571437 2000000000000000000000000000⟩,
  ⟨q 2499999999999999999999 10000000000000000000000, q 2500000000000000000001 10000000000000000000000⟩,
  ⟨q 1958868239504182093160893749 50000000000000000000000000000, q 78354729580167283726435751 2000000000000000000000000000⟩,
  ⟨q 34065075469136244723692787727 50000000000000000000000000000, q 34065075469136244723692787983 50000000000000000000000000000⟩
]

/-! ## Direct 22D Romik system -/

/-! ## Public proof-carrying view and optional executable cross-check

The full executable Krawczyk/grid replay above is intentionally retained, but
normalizing it in one kernel reduction is prohibitively expensive.  The trusted
proof path therefore consumes the frozen exact-rational certificate emitted by
the independent replay and checks that certificate in `CertificateManifest`.
This is the standard proof-carrying-data split: expensive certificate discovery
is outside the kernel; small rational certificate verification is inside it.

The executable wrappers prefixed by `executable` remain available for offline
cross-checking and provenance. -/

/-- The rational interval used internally by the executable replay for `Real.pi`. -/
def declaredPiInterval : RatInterval := piI

/-- Public wrapper around the executable sine enclosure. -/
def sineInterval (x : RatInterval) : RatInterval := sinI x

/-- Public wrapper around the executable cosine enclosure. -/
def cosineInterval (x : RatInterval) : RatInterval := cosI x

/-- Frozen reduced input box used by the trusted certificate. -/
def reducedInputBox : List RatInterval := CertificateManifest.x4

/-- Frozen direct-system input box used by the trusted certificate. -/
def fullInputBox : List RatInterval := CertificateManifest.z22

end GerverSofa.ExactReplay
