import GerverSofa.KernelOnly.ReducedADSoundness

/-!
# Concrete interval-AD soundness for the direct 22D Romik system

The direct system contains five trigonometric path pieces, three derivative
pieces and six matching pairs.  To avoid 22 unrelated derivative proofs, this
file evaluates every expression in a proof-carrying dual object.  Its first
projection is the exact executable `ExactReplay.D`; its second projection is a
smooth real scalar model; and its third field is the constructor-level
soundness theorem from `ADCoreSoundness`.
-/

noncomputable section

namespace GerverSofa

open RatInterval

namespace Romik

/-! ## Exact identification of the 22D input box

The 22 coordinates are kept as separate tiny lemmas.  This is deliberately
chunked: expanding all 44 rational endpoint inequalities in one `simp` call
exhausts the default heartbeat budget even though every coordinate identity is
individually trivial. -/
private theorem fullInputBox_coord_0_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 0) (x 0) ↔
      qR (-21032242207268875141628571849) 100000000000000000000000000000 ≤ x 0 ∧
      x 0 ≤ qR (-21032242207268875141608571849) 100000000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_1_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 1) (x 1) ↔
      qR 2499999999999999999999 10000000000000000000000 ≤ x 1 ∧
      x 1 ≤ qR 2500000000000000000001 10000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_2_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 2) (x 2) ↔
      qR (-91917929277159332227479610289) 100000000000000000000000000000 ≤ x 2 ∧
      x 2 ≤ qR (-91917929277159332227459610289) 100000000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_3_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 3) (x 3) ↔
      qR 29525413734425341573853797657 62500000000000000000000000000 ≤ x 3 ∧
      x 3 ≤ qR 29525413734425341573866297657 62500000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_4_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 4) (x 4) ↔
      qR (-15344080735756291713875357283) 25000000000000000000000000000 ≤ x 4 ∧
      x 4 ≤ qR (-15344080735756291713870357283) 25000000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_5_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 5) (x 5) ↔
      qR 17792529580064437214538861001 20000000000000000000000000000 ≤ x 5 ∧
      x 5 ≤ qR 17792529580064437214542861001 20000000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_6_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 6) (x 6) ↔
      qR (-15417358304445500741761623987) 50000000000000000000000000000 ≤ x 6 ∧
      x 6 ≤ qR (-15417358304445500741751623987) 50000000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_7_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 7) (x 7) ↔
      qR 29525413734425341573853797657 62500000000000000000000000000 ≤ x 7 ∧
      x 7 ≤ qR 29525413734425341573866297657 62500000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_8_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 8) (x 8) ↔
      qR (-20344080735756291713874857283) 20000000000000000000000000000 ≤ x 8 ∧
      x 8 ≤ qR (-20344080735756291713870857283) 20000000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_9_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 9) (x 9) ↔
      qR 2499999999999999999999 10000000000000000000000 ≤ x 9 ∧
      x 9 ≤ qR 2500000000000000000001 10000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_10_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 10) (x 10) ↔
      qR 2420644844145377502832171437 2000000000000000000000000000 ≤ x 10 ∧
      x 10 ≤ qR 2420644844145377502832571437 2000000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_11_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 11) (x 11) ↔
      qR (-2500000000000000000001) 10000000000000000000000 ≤ x 11 ∧
      x 11 ≤ qR (-2499999999999999999999) 10000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_12_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 12) (x 12) ↔
      qR (-52762459802678462416060380937) 100000000000000000000000000000 ≤ x 12 ∧
      x 12 ≤ qR (-52762459802678462416040380937) 100000000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_13_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 13) (x 13) ↔
      qR 92025838516063762289360579501 100000000000000000000000000000 ≤ x 13 ∧
      x 13 ≤ qR 92025838516063762289380579501 100000000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_14_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 14) (x 14) ↔
      qR 313022761424232933776114655193 500000000000000000000000000000 ≤ x 14 ∧
      x 14 ≤ qR 313022761424232933776214655193 500000000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_15_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 15) (x 15) ↔
      qR (-151160128631428920268654781) 160000000000000000000000000 ≤ x 15 ∧
      x 15 ≤ qR (-151160128631428920268622781) 160000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_16_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 16) (x 16) ↔
      qR 1641278451780291167220080819 1250000000000000000000000000 ≤ x 16 ∧
      x 16 ≤ qR 1641278451780291167220330819 1250000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_17_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 17) (x 17) ↔
      qR (-105076534082910887440587258861) 200000000000000000000000000000 ≤ x 17 ∧
      x 17 ≤ qR (-105076534082910887440547258861) 200000000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_18_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 18) (x 18) ↔
      qR 2420644844145377502832171437 2000000000000000000000000000 ≤ x 18 ∧
      x 18 ≤ qR 2420644844145377502832571437 2000000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_19_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 19) (x 19) ↔
      qR 2499999999999999999999 10000000000000000000000 ≤ x 19 ∧
      x 19 ≤ qR 2500000000000000000001 10000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_20_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 20) (x 20) ↔
      qR 1958868239504182093160893749 50000000000000000000000000000 ≤ x 20 ∧
      x 20 ≤ qR 78354729580167283726435751 2000000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]
private theorem fullInputBox_coord_21_iff (x : Vec 22) :
    Contains (ExactReplay.getI ExactReplay.fullInputBox 21) (x 21) ↔
      qR 34065075469136244723692787727 50000000000000000000000000000 ≤ x 21 ∧
      x 21 ≤ qR 34065075469136244723692787983 50000000000000000000000000000 := by
  simp [ExactReplay.fullInputBox, CertificateManifest.z22,
    CertificateManifest.q, ExactReplay.getI, RatInterval.Contains, qR]

/-- The 22 frozen rational intervals are exactly the named direct-system box. -/
theorem inputBox_exact (x : Vec 22) :
    x ∈ vectorBox ↔ EnclosesVec ExactReplay.fullInputBox x := by
  constructor
  · intro hx
    change coordEquiv.symm x ∈ box at hx
    dsimp [box, coordEquiv] at hx
    rcases hx with ⟨h0lo, h0hi, h1lo, h1hi, h2lo, h2hi, h3lo, h3hi, h4lo, h4hi, h5lo, h5hi, h6lo, h6hi, h7lo, h7hi, h8lo, h8hi, h9lo, h9hi, h10lo, h10hi, h11lo, h11hi, h12lo, h12hi, h13lo, h13hi, h14lo, h14hi, h15lo, h15hi, h16lo, h16hi, h17lo, h17hi, h18lo, h18hi, h19lo, h19hi, h20lo, h20hi, h21lo, h21hi⟩
    refine ⟨?_, ?_⟩
    · norm_num [ExactReplay.fullInputBox, CertificateManifest.z22]
    · intro i
      fin_cases i
      · exact (fullInputBox_coord_0_iff x).2 ⟨h0lo, h0hi⟩
      · exact (fullInputBox_coord_1_iff x).2 ⟨h1lo, h1hi⟩
      · exact (fullInputBox_coord_2_iff x).2 ⟨h2lo, h2hi⟩
      · exact (fullInputBox_coord_3_iff x).2 ⟨h3lo, h3hi⟩
      · exact (fullInputBox_coord_4_iff x).2 ⟨h4lo, h4hi⟩
      · exact (fullInputBox_coord_5_iff x).2 ⟨h5lo, h5hi⟩
      · exact (fullInputBox_coord_6_iff x).2 ⟨h6lo, h6hi⟩
      · exact (fullInputBox_coord_7_iff x).2 ⟨h7lo, h7hi⟩
      · exact (fullInputBox_coord_8_iff x).2 ⟨h8lo, h8hi⟩
      · exact (fullInputBox_coord_9_iff x).2 ⟨h9lo, h9hi⟩
      · exact (fullInputBox_coord_10_iff x).2 ⟨h10lo, h10hi⟩
      · exact (fullInputBox_coord_11_iff x).2 ⟨h11lo, h11hi⟩
      · exact (fullInputBox_coord_12_iff x).2 ⟨h12lo, h12hi⟩
      · exact (fullInputBox_coord_13_iff x).2 ⟨h13lo, h13hi⟩
      · exact (fullInputBox_coord_14_iff x).2 ⟨h14lo, h14hi⟩
      · exact (fullInputBox_coord_15_iff x).2 ⟨h15lo, h15hi⟩
      · exact (fullInputBox_coord_16_iff x).2 ⟨h16lo, h16hi⟩
      · exact (fullInputBox_coord_17_iff x).2 ⟨h17lo, h17hi⟩
      · exact (fullInputBox_coord_18_iff x).2 ⟨h18lo, h18hi⟩
      · exact (fullInputBox_coord_19_iff x).2 ⟨h19lo, h19hi⟩
      · exact (fullInputBox_coord_20_iff x).2 ⟨h20lo, h20hi⟩
      · exact (fullInputBox_coord_21_iff x).2 ⟨h21lo, h21hi⟩
  · rintro ⟨_hlen, hx⟩
    change coordEquiv.symm x ∈ box
    dsimp [box, coordEquiv]
    have h0 := (fullInputBox_coord_0_iff x).1 (hx (0 : Fin 22))
    have h1 := (fullInputBox_coord_1_iff x).1 (hx (1 : Fin 22))
    have h2 := (fullInputBox_coord_2_iff x).1 (hx (2 : Fin 22))
    have h3 := (fullInputBox_coord_3_iff x).1 (hx (3 : Fin 22))
    have h4 := (fullInputBox_coord_4_iff x).1 (hx (4 : Fin 22))
    have h5 := (fullInputBox_coord_5_iff x).1 (hx (5 : Fin 22))
    have h6 := (fullInputBox_coord_6_iff x).1 (hx (6 : Fin 22))
    have h7 := (fullInputBox_coord_7_iff x).1 (hx (7 : Fin 22))
    have h8 := (fullInputBox_coord_8_iff x).1 (hx (8 : Fin 22))
    have h9 := (fullInputBox_coord_9_iff x).1 (hx (9 : Fin 22))
    have h10 := (fullInputBox_coord_10_iff x).1 (hx (10 : Fin 22))
    have h11 := (fullInputBox_coord_11_iff x).1 (hx (11 : Fin 22))
    have h12 := (fullInputBox_coord_12_iff x).1 (hx (12 : Fin 22))
    have h13 := (fullInputBox_coord_13_iff x).1 (hx (13 : Fin 22))
    have h14 := (fullInputBox_coord_14_iff x).1 (hx (14 : Fin 22))
    have h15 := (fullInputBox_coord_15_iff x).1 (hx (15 : Fin 22))
    have h16 := (fullInputBox_coord_16_iff x).1 (hx (16 : Fin 22))
    have h17 := (fullInputBox_coord_17_iff x).1 (hx (17 : Fin 22))
    have h18 := (fullInputBox_coord_18_iff x).1 (hx (18 : Fin 22))
    have h19 := (fullInputBox_coord_19_iff x).1 (hx (19 : Fin 22))
    have h20 := (fullInputBox_coord_20_iff x).1 (hx (20 : Fin 22))
    have h21 := (fullInputBox_coord_21_iff x).1 (hx (21 : Fin 22))
    exact ⟨h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2, h6.1, h6.2, h7.1, h7.2, h8.1, h8.2, h9.1, h9.2, h10.1, h10.2, h11.1, h11.2, h12.1, h12.2, h13.1, h13.2, h14.1, h14.2, h15.1, h15.2, h16.1, h16.2, h17.1, h17.2, h18.1, h18.2, h19.1, h19.2, h20.1, h20.2, h21.1, h21.2⟩

/-- All four switching times used by the direct evaluator lie in `[0,π/2]`. -/
theorem full_switches_physical {x : Vec 22} (hx : x ∈ vectorBox) :
    (0 ≤ x 20 ∧ x 20 ≤ Real.pi / 2) ∧
    (0 ≤ x 21 ∧ x 21 ≤ Real.pi / 2) ∧
    (0 ≤ Real.pi / 2 - x 21 ∧ Real.pi / 2 - x 21 ≤ Real.pi / 2) ∧
    (0 ≤ Real.pi / 2 - x 20 ∧ Real.pi / 2 - x 20 ≤ Real.pi / 2) := by
  let p := coordEquiv.symm x
  have hp : p ∈ box := hx
  have hphiPos : 0 < p.phi := phi_pos_of_mem_box hp
  have hord : SwitchOrder p := switchOrder_of_mem_box hp
  have htheta0 : 0 ≤ p.theta :=
    le_trans hphiPos.le hord.phi_le_theta
  have hthetaHalf : p.theta ≤ Real.pi / 2 := by
    linarith [hord.theta_le_eta]
  have hphiHalf : p.phi ≤ Real.pi / 2 :=
    le_trans hord.phi_le_theta hthetaHalf
  change
    (0 ≤ p.phi ∧ p.phi ≤ Real.pi / 2) ∧
    (0 ≤ p.theta ∧ p.theta ≤ Real.pi / 2) ∧
    (0 ≤ Real.pi / 2 - p.theta ∧
      Real.pi / 2 - p.theta ≤ Real.pi / 2) ∧
    (0 ≤ Real.pi / 2 - p.phi ∧
      Real.pi / 2 - p.phi ≤ Real.pi / 2)
  constructor
  · exact ⟨hphiPos.le, hphiHalf⟩
  constructor
  · exact ⟨htheta0, hthetaHalf⟩
  constructor
  · constructor <;> linarith
  · constructor <;> linarith

/-! ## Proof-carrying dual expressions -/

/-- One executable interval dual paired with its real semantic model. -/
structure SoundDual (n : Nat) (X : Set (Vec n)) where
  d : ExactReplay.D
  model : ScalarModel n
  sound : DSoundOn X d model

namespace SoundDual

variable {n : Nat} {X : Set (Vec n)}

def const (z : RatInterval) (c : ℝ) (h : Contains z c) : SoundDual n X :=
  ⟨ExactReplay.D.const z n, ScalarModel.const n c, DSoundOn.const h⟩

def pointConst (q : ℚ) : SoundDual n X :=
  ⟨ExactReplay.D.pointConst q n, ScalarModel.const n (q : ℝ),
    DSoundOn.pointConst q⟩

def var (input : RatInterval) (k : Fin n)
    (h : ∀ x ∈ X, Contains input (x k)) : SoundDual n X :=
  ⟨ExactReplay.D.varD input k.1 n, ScalarModel.var n k,
    DSoundOn.varD input k h⟩

def add (a b : SoundDual n X) : SoundDual n X :=
  ⟨ExactReplay.D.addD a.d b.d, ScalarModel.add a.model b.model,
    a.sound.add b.sound⟩

def neg (a : SoundDual n X) : SoundDual n X :=
  ⟨ExactReplay.D.negD a.d, ScalarModel.neg a.model, a.sound.neg⟩

def sub (a b : SoundDual n X) : SoundDual n X :=
  ⟨ExactReplay.D.subD a.d b.d, ScalarModel.sub a.model b.model,
    a.sound.sub b.sound⟩

def mul (a b : SoundDual n X) : SoundDual n X :=
  ⟨ExactReplay.D.mulD a.d b.d, ScalarModel.mul a.model b.model,
    a.sound.mul b.sound⟩

def scale (q : ℚ) (a : SoundDual n X) : SoundDual n X :=
  ⟨ExactReplay.D.scaleD q a.d, ScalarModel.scale q a.model,
    DSoundOn.scale q a.sound⟩

def sin (a : SoundDual n X)
    (h : ∀ x ∈ X, 0 ≤ a.model.value x ∧
      a.model.value x ≤ Real.pi / 2) : SoundDual n X :=
  ⟨ExactReplay.D.sinD a.d, ScalarModel.sin a.model, a.sound.sin h⟩

def cos (a : SoundDual n X)
    (h : ∀ x ∈ X, 0 ≤ a.model.value x ∧
      a.model.value x ≤ Real.pi / 2) : SoundDual n X :=
  ⟨ExactReplay.D.cosD a.d, ScalarModel.cos a.model, a.sound.cos h⟩

instance : Add (SoundDual n X) := ⟨add⟩
instance : Neg (SoundDual n X) := ⟨neg⟩
instance : Sub (SoundDual n X) := ⟨sub⟩
instance : Mul (SoundDual n X) := ⟨mul⟩
instance : HMul ℚ (SoundDual n X) (SoundDual n X) := ⟨scale⟩

/-! Small projection lemmas keep the simplifier away from the proof fields of
`SoundDual`.  All are definitional equalities. -/
@[simp] theorem const_model_value (z : RatInterval) (c : ℝ)
    (h : Contains z c) (x : Vec n) :
    (const z c h : SoundDual n X).model.value x = c := rfl

@[simp] theorem pointConst_model_value (q : ℚ) (x : Vec n) :
    (pointConst q : SoundDual n X).model.value x = (q : ℝ) := rfl

@[simp] theorem var_model_value (input : RatInterval) (k : Fin n)
    (h : ∀ x ∈ X, Contains input (x k)) (x : Vec n) :
    (var input k h : SoundDual n X).model.value x = x k := rfl

@[simp] theorem add_model_value (a b : SoundDual n X) (x : Vec n) :
    (a + b).model.value x = a.model.value x + b.model.value x := rfl

@[simp] theorem neg_model_value (a : SoundDual n X) (x : Vec n) :
    (-a).model.value x = -a.model.value x := rfl

@[simp] theorem sub_model_value (a b : SoundDual n X) (x : Vec n) :
    (a - b).model.value x = a.model.value x - b.model.value x := rfl

@[simp] theorem mul_model_value (a b : SoundDual n X) (x : Vec n) :
    (a * b).model.value x = a.model.value x * b.model.value x := rfl

@[simp] theorem scale_model_value (q : ℚ) (a : SoundDual n X) (x : Vec n) :
    (q * a).model.value x = (q : ℝ) * a.model.value x := rfl

@[simp] theorem sin_model_value (a : SoundDual n X)
    (h : ∀ x ∈ X, 0 ≤ a.model.value x ∧ a.model.value x ≤ Real.pi / 2)
    (x : Vec n) :
    (sin a h).model.value x = Real.sin (a.model.value x) := rfl

@[simp] theorem cos_model_value (a : SoundDual n X)
    (h : ∀ x ∈ X, 0 ≤ a.model.value x ∧ a.model.value x ≤ Real.pi / 2)
    (x : Vec n) :
    (cos a h).model.value x = Real.cos (a.model.value x) := rfl

end SoundDual

/-- A certified physical angle, used to justify every sine/cosine constructor. -/
structure AngleDual (n : Nat) (X : Set (Vec n)) where
  dual : SoundDual n X
  physical : ∀ x ∈ X, 0 ≤ dual.model.value x ∧
    dual.model.value x ≤ Real.pi / 2

namespace AngleDual

variable {n : Nat} {X : Set (Vec n)}

def sin (t : AngleDual n X) : SoundDual n X :=
  SoundDual.sin t.dual t.physical

def cos (t : AngleDual n X) : SoundDual n X :=
  SoundDual.cos t.dual t.physical

@[simp] theorem sin_model_value (t : AngleDual n X) (x : Vec n) :
    t.sin.model.value x = Real.sin (t.dual.model.value x) := rfl

@[simp] theorem cos_model_value (t : AngleDual n X) (x : Vec n) :
    t.cos.model.value x = Real.cos (t.dual.model.value x) := rfl

end AngleDual

/-- Named proof-carrying versions of all direct-system variables. -/
structure FullVars (X : Set (Vec 22)) where
  k11 : SoundDual 22 X
  k12 : SoundDual 22 X
  k21 : SoundDual 22 X
  k22 : SoundDual 22 X
  k31 : SoundDual 22 X
  k32 : SoundDual 22 X
  k41 : SoundDual 22 X
  k42 : SoundDual 22 X
  k51 : SoundDual 22 X
  k52 : SoundDual 22 X
  a1 : SoundDual 22 X
  a2 : SoundDual 22 X
  b1 : SoundDual 22 X
  b2 : SoundDual 22 X
  c1 : SoundDual 22 X
  c2 : SoundDual 22 X
  d1 : SoundDual 22 X
  d2 : SoundDual 22 X
  e1 : SoundDual 22 X
  e2 : SoundDual 22 X

/-- The 22 coordinate variables equipped with their input-enclosure proofs. -/
def inputDual (i : Fin 22) : SoundDual 22 vectorBox :=
  SoundDual.var (ExactReplay.getI ExactReplay.fullInputBox i.1) i (by
    intro x hx
    exact ((inputBox_exact x).1 hx).2 i)

@[simp] theorem inputDual_model_value (i : Fin 22) (x : Vec 22) :
    (inputDual i).model.value x = x i := rfl

/-- Named first twenty variables in verifier order. -/
def fullVars : FullVars vectorBox where
  k11 := inputDual 0
  k12 := inputDual 1
  k21 := inputDual 2
  k22 := inputDual 3
  k31 := inputDual 4
  k32 := inputDual 5
  k41 := inputDual 6
  k42 := inputDual 7
  k51 := inputDual 8
  k52 := inputDual 9
  a1 := inputDual 10
  a2 := inputDual 11
  b1 := inputDual 12
  b2 := inputDual 13
  c1 := inputDual 14
  c2 := inputDual 15
  d1 := inputDual 16
  d2 := inputDual 17
  e1 := inputDual 18
  e2 := inputDual 19

/-- Exact proof-carrying π constant. -/
def piDual : SoundDual 22 vectorBox :=
  SoundDual.const ExactReplay.piI Real.pi ExactReplay.piI_contains_pi

@[simp] theorem piDual_model_value (x : Vec 22) :
    piDual.model.value x = Real.pi := rfl

/-- First switching angle. -/
def phiDual : AngleDual 22 vectorBox where
  dual := inputDual 20
  physical := by
    intro x hx
    simpa only [inputDual_model_value] using
      (full_switches_physical hx).1

@[simp] theorem phiDual_model_value (x : Vec 22) :
    phiDual.dual.model.value x = x 20 := rfl

/-- Second switching angle. -/
def thetaDual : AngleDual 22 vectorBox where
  dual := inputDual 21
  physical := by
    intro x hx
    simpa only [inputDual_model_value] using
      (full_switches_physical hx).2.1

@[simp] theorem thetaDual_model_value (x : Vec 22) :
    thetaDual.dual.model.value x = x 21 := rfl

private theorem eta_raw_model_value (x : Vec 22) :
    (((1 / 2 : ℚ) * piDual - thetaDual.dual).model.value x) =
      Real.pi / 2 - x 21 := by
  simp <;> ring

/-- Reflected third switching angle `π/2-θ`. -/
def etaDual : AngleDual 22 vectorBox where
  dual := (1 / 2 : ℚ) * piDual - thetaDual.dual
  physical := by
    intro x hx
    change
      0 ≤ (((1 / 2 : ℚ) * piDual - thetaDual.dual).model.value x) ∧
      (((1 / 2 : ℚ) * piDual - thetaDual.dual).model.value x) ≤ Real.pi / 2
    rw [eta_raw_model_value]
    exact (full_switches_physical hx).2.2.1

@[simp] theorem etaDual_model_value (x : Vec 22) :
    etaDual.dual.model.value x = Real.pi / 2 - x 21 := by
  exact eta_raw_model_value x

private theorem tau_raw_model_value (x : Vec 22) :
    (((1 / 2 : ℚ) * piDual - phiDual.dual).model.value x) =
      Real.pi / 2 - x 20 := by
  simp <;> ring

/-- Reflected fourth switching angle `π/2-φ`. -/
def tauDual : AngleDual 22 vectorBox where
  dual := (1 / 2 : ℚ) * piDual - phiDual.dual
  physical := by
    intro x hx
    change
      0 ≤ (((1 / 2 : ℚ) * piDual - phiDual.dual).model.value x) ∧
      (((1 / 2 : ℚ) * piDual - phiDual.dual).model.value x) ≤ Real.pi / 2
    rw [tau_raw_model_value]
    exact (full_switches_physical hx).2.2.2

@[simp] theorem tauDual_model_value (x : Vec 22) :
    tauDual.dual.model.value x = Real.pi / 2 - x 20 := by
  exact tau_raw_model_value x

/-- Rotation of a proof-carrying body-frame vector. -/
def rotDual (t : AngleDual 22 vectorBox)
    (z1 z2 : SoundDual 22 vectorBox) :
    SoundDual 22 vectorBox × SoundDual 22 vectorBox :=
  let ct := t.cos
  let st := t.sin
  (ct * z1 - st * z2, st * z1 + ct * z2)

/-- One proof-carrying path piece. -/
def pathPieceDual (j : Nat) (t : AngleDual 22 vectorBox)
    (p : FullVars vectorBox := fullVars) :
    SoundDual 22 vectorBox × SoundDual 22 vectorBox :=
  let one : SoundDual 22 vectorBox := SoundDual.pointConst 1
  let half : SoundDual 22 vectorBox := SoundDual.pointConst (1 / 2)
  let quarter : SoundDual 22 vectorBox := SoundDual.pointConst (1 / 4)
  let ct := t.cos
  let st := t.sin
  let data : SoundDual 22 vectorBox × SoundDual 22 vectorBox ×
      SoundDual 22 vectorBox × SoundDual 22 vectorBox :=
    if j = 1 then
      (p.a1 * ct + p.a2 * st - one,
       -p.a2 * ct + p.a1 * st - half,
       p.k11, p.k12)
    else if j = 2 then
      (-quarter * t.dual * t.dual + p.b1 * t.dual + p.b2,
       half * t.dual - p.b1 - one,
       p.k21, p.k22)
    else if j = 3 then
      (p.c1 - t.dual, p.c2 + t.dual, p.k31, p.k32)
    else if j = 4 then
      (-half * t.dual + p.d1 - one,
       -quarter * t.dual * t.dual + p.d1 * t.dual + p.d2,
       p.k41, p.k42)
    else
      (p.e1 * ct + p.e2 * st - half,
       -p.e2 * ct + p.e1 * st - one,
       p.k51, p.k52)
  let rr := rotDual t data.1 data.2.1
  (rr.1 + data.2.2.1, rr.2 + data.2.2.2)

/-- Body-frame derivative coefficients for one phase. -/
def alphaBetaDual (j : Nat) (t : AngleDual 22 vectorBox)
    (p : FullVars vectorBox := fullVars) :
    SoundDual 22 vectorBox × SoundDual 22 vectorBox :=
  let one : SoundDual 22 vectorBox := SoundDual.pointConst 1
  let half : SoundDual 22 vectorBox := SoundDual.pointConst (1 / 2)
  let quarter : SoundDual 22 vectorBox := SoundDual.pointConst (1 / 4)
  let ct := t.cos
  let st := t.sin
  if j = 1 then
    (-(2 : ℚ) * p.a1 * st + (2 : ℚ) * p.a2 * ct + half,
     (2 : ℚ) * p.a1 * ct + (2 : ℚ) * p.a2 * st - one)
  else if j = 2 then
    (one + (2 : ℚ) * p.b1 - t.dual,
     -quarter * t.dual * t.dual + p.b1 * t.dual + p.b2 + half)
  else if j = 3 then
    (-one - p.c2 - t.dual, one + p.c1 - t.dual)
  else if j = 4 then
    (quarter * t.dual * t.dual - p.d1 * t.dual - p.d2 - half,
     (2 : ℚ) * p.d1 - one - t.dual)
  else
    (one - (2 : ℚ) * p.e1 * st + (2 : ℚ) * p.e2 * ct,
     (2 : ℚ) * p.e1 * ct + (2 : ℚ) * p.e2 * st - half)

/-- World-frame derivative piece. -/
def pathPrimeDual (j : Nat) (t : AngleDual 22 vectorBox)
    (p : FullVars vectorBox := fullVars) :
    SoundDual 22 vectorBox × SoundDual 22 vectorBox :=
  let ab := alphaBetaDual j t p
  rotDual t ab.1 ab.2

/-- The complete proof-carrying direct system in manuscript order. -/
def fullDualOutput : List (SoundDual 22 vectorBox) :=
  let p := fullVars
  let halfPi := (1 / 2 : ℚ) * piDual
  let quarterPi := (1 / 4 : ℚ) * piDual
  let one : SoundDual 22 vectorBox := SoundDual.pointConst 1
  let quarter : SoundDual 22 vectorBox := SoundDual.pointConst (1 / 4)
  let first : List (SoundDual 22 vectorBox) := [
    p.e1 - p.a1,
    p.e2 + p.a2,
    p.d1 + p.b1 - quarterPi,
    p.d2 - p.b2 - quarterPi * ((2 : ℚ) * p.b1 - quarterPi),
    p.c2 - p.c1 + halfPi,
    p.k11 - one + p.a1,
    p.k12 - quarter,
    p.a2 + quarter
  ]
  let pairs := [
    (pathPieceDual 1 phiDual p, pathPieceDual 2 phiDual p),
    (pathPrimeDual 1 phiDual p, pathPrimeDual 2 phiDual p),
    (pathPieceDual 2 thetaDual p, pathPieceDual 3 thetaDual p),
    (pathPrimeDual 2 thetaDual p, pathPrimeDual 3 thetaDual p),
    (pathPieceDual 3 etaDual p, pathPieceDual 4 etaDual p),
    (pathPieceDual 4 tauDual p, pathPieceDual 5 tauDual p)
  ]
  let matchEqs := pairs.flatMap (fun lr =>
    [lr.1.1 - lr.2.1, lr.1.2 - lr.2.2])
  let lhs := pathPieceDual 1 phiDual p
  let xe := pathPieceDual 3 etaDual p
  let ae := (alphaBetaDual 3 etaDual p).1
  let be :=
    (xe.1 - ae * etaDual.sin, xe.2 + ae * etaDual.cos)
  first ++ matchEqs ++ [lhs.1 - be.1, lhs.2 - be.2]

/-! Public-shape unfold lemmas for the three derivative path pieces.

`Systems.lean` deliberately hides the helper `pathPrimeFromAB`.  When `system`
is unfolded outside that file, the private helper survives as an inaccessible
constant, so `ring` cannot see that the right-hand side is just a rotation.
These `rfl` lemmas expose exactly the public normal form needed by the four
derivative-matching equations. -/
private theorem pathPrime1_eq_rot (p : Params) (t : ℝ) :
    pathPrime1 p t = rot t (alphaBeta1 p t) := rfl

private theorem pathPrime2_eq_rot (p : Params) (t : ℝ) :
    pathPrime2 p t = rot t (alphaBeta2 p t) := rfl

private theorem pathPrime3_eq_rot (p : Params) (t : ℝ) :
    pathPrime3 p t = rot t (alphaBeta3 p t) := rfl

/-! The semantic identification is split coordinatewise so each normalization
gets its own heartbeat budget.  A single 22-way `fin_cases <;> simp <;> ring`
command is mathematically fine but deterministically exhausts 200000 heartbeats. -/

private theorem fullDualOutput_model_eq_0 (x : Vec 22) :
    ((fullDualOutput.getD 0 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (0 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3, alphaBeta4, alphaBeta5]
  <;> ring

private theorem fullDualOutput_model_eq_1 (x : Vec 22) :
    ((fullDualOutput.getD 1 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (1 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3, alphaBeta4, alphaBeta5]
  <;> ring

private theorem fullDualOutput_model_eq_2 (x : Vec 22) :
    ((fullDualOutput.getD 2 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (2 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3, alphaBeta4, alphaBeta5]
  <;> ring

private theorem fullDualOutput_model_eq_3 (x : Vec 22) :
    ((fullDualOutput.getD 3 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (3 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3, alphaBeta4, alphaBeta5]
  <;> ring

private theorem fullDualOutput_model_eq_4 (x : Vec 22) :
    ((fullDualOutput.getD 4 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (4 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3, alphaBeta4, alphaBeta5]
  <;> ring

private theorem fullDualOutput_model_eq_5 (x : Vec 22) :
    ((fullDualOutput.getD 5 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (5 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3, alphaBeta4, alphaBeta5]
  <;> ring

private theorem fullDualOutput_model_eq_6 (x : Vec 22) :
    ((fullDualOutput.getD 6 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (6 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3, alphaBeta4, alphaBeta5]
  <;> ring

private theorem fullDualOutput_model_eq_7 (x : Vec 22) :
    ((fullDualOutput.getD 7 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (7 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3, alphaBeta4, alphaBeta5]
  <;> ring

private theorem fullDualOutput_model_eq_8 (x : Vec 22) :
    ((fullDualOutput.getD 8 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (8 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3, alphaBeta4, alphaBeta5]
  <;> ring

private theorem fullDualOutput_model_eq_9 (x : Vec 22) :
    ((fullDualOutput.getD 9 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (9 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3, alphaBeta4, alphaBeta5]
  <;> ring

private theorem fullDualOutput_model_eq_10 (x : Vec 22) :
    ((fullDualOutput.getD 10 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (10 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1_eq_rot,
    pathPrime2_eq_rot, pathPrime3_eq_rot, alphaBeta1, alphaBeta2, alphaBeta3,
    alphaBeta4, alphaBeta5]
  <;> ring

private theorem fullDualOutput_model_eq_11 (x : Vec 22) :
    ((fullDualOutput.getD 11 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (11 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1_eq_rot,
    pathPrime2_eq_rot, pathPrime3_eq_rot, alphaBeta1, alphaBeta2, alphaBeta3,
    alphaBeta4, alphaBeta5]
  <;> ring

private theorem fullDualOutput_model_eq_12 (x : Vec 22) :
    ((fullDualOutput.getD 12 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (12 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3, alphaBeta4, alphaBeta5]
  <;> ring

private theorem fullDualOutput_model_eq_13 (x : Vec 22) :
    ((fullDualOutput.getD 13 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (13 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3, alphaBeta4, alphaBeta5]
  <;> ring

private theorem fullDualOutput_model_eq_14 (x : Vec 22) :
    ((fullDualOutput.getD 14 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (14 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1_eq_rot,
    pathPrime2_eq_rot, pathPrime3_eq_rot, alphaBeta1, alphaBeta2, alphaBeta3,
    alphaBeta4, alphaBeta5]
  <;> ring

private theorem fullDualOutput_model_eq_15 (x : Vec 22) :
    ((fullDualOutput.getD 15 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (15 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1_eq_rot,
    pathPrime2_eq_rot, pathPrime3_eq_rot, alphaBeta1, alphaBeta2, alphaBeta3,
    alphaBeta4, alphaBeta5]
  <;> ring

private theorem fullDualOutput_model_eq_16 (x : Vec 22) :
    ((fullDualOutput.getD 16 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (16 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3, alphaBeta4, alphaBeta5]
  <;> ring

private theorem fullDualOutput_model_eq_17 (x : Vec 22) :
    ((fullDualOutput.getD 17 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (17 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3, alphaBeta4, alphaBeta5]
  <;> ring

private theorem fullDualOutput_model_eq_18 (x : Vec 22) :
    ((fullDualOutput.getD 18 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (18 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3, alphaBeta4, alphaBeta5]
  <;> ring

private theorem fullDualOutput_model_eq_19 (x : Vec 22) :
    ((fullDualOutput.getD 19 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (19 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3, alphaBeta4, alphaBeta5]
  <;> ring

private theorem fullDualOutput_model_eq_20 (x : Vec 22) :
    ((fullDualOutput.getD 20 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (20 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3, alphaBeta4, alphaBeta5]
  <;> ring

private theorem fullDualOutput_model_eq_21 (x : Vec 22) :
    ((fullDualOutput.getD 21 (SoundDual.pointConst 0)).model.value x) =
      vectorSystem x (21 : Fin 22) := by
  simp [fullDualOutput, fullVars, rotDual, pathPieceDual,
    alphaBetaDual, pathPrimeDual, vectorSystem, coordEquiv, system, rot,
    addK, path1, path2, path3, path4, path5, pathPrime1, pathPrime2,
    pathPrime3, alphaBeta1, alphaBeta2, alphaBeta3, alphaBeta4, alphaBeta5]
  <;> ring

/-- The real models carried by `fullDualOutput` are exactly the 22 manuscript
functions in finite-vector coordinates. -/
theorem fullDualOutput_model_eq (x : Vec 22) :
    (fun i : Fin 22 =>
      ((fullDualOutput.getD i.1
        (SoundDual.pointConst 0)).model.value x)) = vectorSystem x := by
  funext i
  fin_cases i
  · exact fullDualOutput_model_eq_0 x
  · exact fullDualOutput_model_eq_1 x
  · exact fullDualOutput_model_eq_2 x
  · exact fullDualOutput_model_eq_3 x
  · exact fullDualOutput_model_eq_4 x
  · exact fullDualOutput_model_eq_5 x
  · exact fullDualOutput_model_eq_6 x
  · exact fullDualOutput_model_eq_7 x
  · exact fullDualOutput_model_eq_8 x
  · exact fullDualOutput_model_eq_9 x
  · exact fullDualOutput_model_eq_10 x
  · exact fullDualOutput_model_eq_11 x
  · exact fullDualOutput_model_eq_12 x
  · exact fullDualOutput_model_eq_13 x
  · exact fullDualOutput_model_eq_14 x
  · exact fullDualOutput_model_eq_15 x
  · exact fullDualOutput_model_eq_16 x
  · exact fullDualOutput_model_eq_17 x
  · exact fullDualOutput_model_eq_18 x
  · exact fullDualOutput_model_eq_19 x
  · exact fullDualOutput_model_eq_20 x
  · exact fullDualOutput_model_eq_21 x

end Romik

end GerverSofa
