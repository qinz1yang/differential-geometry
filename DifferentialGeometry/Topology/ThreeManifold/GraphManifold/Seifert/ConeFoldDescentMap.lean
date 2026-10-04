import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldDescentPhase
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FilledCarrier
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PantsGeometry

/-!
# The total-space fold of the one-cone block

In the log coordinates `p = (x, log y, s)` of `ModelCoordinates` (`logPoint p = x + i e^{log y}`),
the fold of the block `(p, ⊤, ⊤)` is `liftMap p = coneLift (f (logPoint p), e^{2πis} Ψ⁻¹)` off the
cone fibre, with `Ψ = foldPhase q` from `ConeFoldDescentPhase`, and the screw tube
`tubeMap p = (3 ω e^{2πias}, e^{2πips})` on the cone fibre; `totalMap` selects between them and
`tubeMap_eq_liftMap` shows that they agree near the apex, where `f` is the branched model and `Ψ =
unitOf ω ^ q`. The mirror half is `mirrorMap p = conjMap (totalMap (flipMap p))` for `x < 0`, where
`flipMap (x, Y, s) = (-x, Y, -s)` lifts the reflection `σ₀` and `conjMap (z, w) = (conj z, w⁻¹)`
is the orientation-reversing involution of `filledSet` covering `u ↦ conj u`. Base points:
`conePoint (liftMap p) = f (logPoint p)` and `conePoint (tubeMap p) = coneApexOne p (logPoint p)`.
Smoothness of all pieces (as maps `𝓡 3 → PlaneCircleModel`) is proved pointwise.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology
open DifferentialGeometry GC.GraphManifold GC.Geometry
open scoped ContDiff ComplexConjugate Manifold

universe u

namespace GC.Seifert

theorem unitOf_pos_smul {r : ℝ} (hr : 0 < r) {w : ℂ} (hw : w ≠ 0) :
    unitOf ((r : ℂ) * w) = unitOf w := by
  have h : (r : ℂ) * w = (r * ‖w‖ : ℝ) • (unitOf w : ℂ) := by
    rw [mul_smul, norm_smul_unitOf, Complex.real_smul]
  rw [h, unitOf_smul (mul_pos hr (norm_pos_iff.mpr hw))]

theorem unitOf_three_mul {w : ℂ} (hw : w ≠ 0) : unitOf (3 * w) = unitOf w := by
  have h := unitOf_pos_smul (by norm_num : (0 : ℝ) < 3) hw
  push_cast at h
  exact h

theorem coe_logPoint' (p : ModelCoordinates) : (logPoint p : ℂ) = ⟨p 0, Real.exp (p 1)⟩ := by
  rw [coe_logPoint]
  apply Complex.ext <;> simp [-Complex.ofReal_exp]

theorem logPoint_im_pos (p : ModelCoordinates) : 0 < (logPoint p : ℂ).im := by
  rw [coe_logPoint']
  exact Real.exp_pos _

theorem contMDiff_coe_logPoint' :
    ContMDiff (𝓡 3) 𝓘(ℝ, ℂ) ∞ (fun p : ModelCoordinates => (logPoint p : ℂ)) :=
  contDiff_coe_logPoint.contMDiff

def filledBase : Set ℂ := {u | ‖u‖ < 3 ∧ 1 / 2 < ‖u + 3 / 2‖}

theorem filledFunction_neg_iff (u : ℂ) :
    ConeFilling.filledFunction u < 0 ↔ u ∈ filledBase := by
  have hc := norm_sub_real_bounds u (-(3 / 2))
  rw [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] at hc
  have h0 := norm_nonneg u
  have hc0 := norm_nonneg (u - ((-(3 / 2) : ℝ) : ℂ))
  have he : u - ((-(3 / 2) : ℝ) : ℂ) = u + 3 / 2 := by push_cast; ring
  change sqDist 0 3 u * sqDist ((-(3 / 2) : ℝ) : ℂ) (1 / 2) u < 0 ↔ ‖u‖ < 3 ∧ 1 / 2 < ‖u + 3 / 2‖
  simp only [sqDist, sub_zero]
  rw [he] at hc hc0 ⊢
  set a := ‖u‖
  set b := ‖u + 3 / 2‖
  constructor
  · intro h
    by_contra hn
    rw [not_and_or, not_lt, not_lt] at hn
    rcases hn with hn | hn
    · have : 0 ≤ (a ^ 2 - 3 ^ 2) * (b ^ 2 - (1 / 2) ^ 2) := mul_nonneg (by nlinarith) (by nlinarith)
      linarith
    · have : 0 ≤ (a ^ 2 - 3 ^ 2) * (b ^ 2 - (1 / 2) ^ 2) :=
        mul_nonneg_of_nonpos_of_nonpos (by nlinarith) (by nlinarith)
      linarith
  · rintro ⟨h1, h2⟩
    exact mul_neg_of_neg_of_pos (by nlinarith) (by nlinarith)

theorem conj_mem_filledBase {u : ℂ} (hu : u ∈ filledBase) : conj u ∈ filledBase := by
  refine ⟨by rw [Complex.norm_conj]; exact hu.1, ?_⟩
  have : conj u + 3 / 2 = conj (u + 3 / 2) := by rw [map_add, map_div₀, map_ofNat, map_ofNat]
  rw [this, Complex.norm_conj]
  exact hu.2

theorem basePlus_subset_filledBase (σ : ConeShape) (hσ : σ.θ₂ = 0) :
    σ.basePlus ⊆ filledBase := fun _ hu => ⟨hu.1, hu.2.2 hσ⟩

theorem mem_filledBase_of_norm_sub_lt {u : ℂ} (hu : ‖u - 3 / 2‖ < 1 / 2) : u ∈ filledBase := by
  have h1 : ‖u‖ ≤ ‖u - 3 / 2‖ + ‖(3 / 2 : ℂ)‖ := by
    calc ‖u‖ = ‖(u - 3 / 2) + 3 / 2‖ := by congr 1; ring
      _ ≤ ‖u - 3 / 2‖ + ‖(3 / 2 : ℂ)‖ := norm_add_le _ _
  have h2 : ‖(3 / 2 : ℂ)‖ = 3 / 2 := by norm_num
  have h3 := norm_sub_le (u + 3 / 2) (u - 3 / 2)
  have h3' : (u + 3 / 2) - (u - 3 / 2) = (3 : ℂ) := by ring
  rw [h3'] at h3
  have h4 : ‖(3 : ℂ)‖ = 3 := by norm_num
  constructor
  · linarith
  · linarith

namespace ConeShape

variable (σ : ConeShape) (c : ConeFilling)

def tubeMap (p : ModelCoordinates) : PlaneLift.{u} × Circle :=
  (ULift.up (3 * coneDisc σ.vertexOne (logPoint p) * (Circle.exp (2 * Real.pi * c.a * p 2) : ℂ)),
    Circle.exp (2 * Real.pi * c.p * p 2))

theorem tubeMap_fst (p : ModelCoordinates) : (σ.tubeMap.{u} c p).1.down =
    3 * coneDisc σ.vertexOne (logPoint p) * (Circle.exp (2 * Real.pi * c.a * p 2) : ℂ) := rfl

theorem tubeMap_snd (p : ModelCoordinates) :
    (σ.tubeMap.{u} c p).2 = Circle.exp (2 * Real.pi * c.p * p 2) := rfl

theorem conePoint_tubeMap (p : ModelCoordinates) :
    c.conePoint (σ.tubeMap.{u} c p) = σ.coneApexOne c.p (logPoint p) := by
  simp only [ConeFilling.conePoint, tubeMap_fst, tubeMap_snd, coneApexOne, Circle.coe_zpow,
    Circle.coe_exp]
  have h1 : (3 : ℂ) * coneDisc σ.vertexOne (logPoint p) *
      exp (((2 * Real.pi * c.a * p 2 : ℝ) : ℂ) * I) / 3 =
      coneDisc σ.vertexOne (logPoint p) * exp (((2 * Real.pi * c.a * p 2 : ℝ) : ℂ) * I) := by
    ring
  have h2 : exp (((2 * Real.pi * c.a * p 2 : ℝ) : ℂ) * I) ^ c.p *
      exp (((2 * Real.pi * c.p * p 2 : ℝ) : ℂ) * I) ^ (-c.a) = 1 := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_int_mul, ← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    push_cast
    ring
  rw [h1, mul_pow, mul_assoc, h2, mul_one]
  push_cast
  ring

theorem coneDisc_ne_zero_of_ne {z : ℂ} (hz : 0 < z.im) (hv : z ≠ σ.vertexOne) :
    coneDisc σ.vertexOne z ≠ 0 := by
  intro h
  apply hv
  have hne := sub_conj_ne_zero σ.vertexOne_im_pos hz
  rw [coneDisc, div_eq_zero_iff] at h
  rcases h with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hne

theorem coneChart_tubeMap {p : ModelCoordinates} (hv : (logPoint p : ℂ) ≠ σ.vertexOne) :
    c.coneChart (σ.tubeMap.{u} c p) =
      (ULift.up (σ.coneApexOne c.p (logPoint p)),
        Circle.exp (2 * Real.pi * p 2) * (unitOf (coneDisc σ.vertexOne (logPoint p)) ^ c.q)⁻¹) := by
  have hω := σ.coneDisc_ne_zero_of_ne (logPoint_im_pos p) hv
  refine Prod.ext (ULift.ext (σ.conePoint_tubeMap c p)) ?_
  change (linearTorusMap c.chartMatrix
    (unitOf (σ.tubeMap.{u} c p).1.down, (σ.tubeMap.{u} c p).2)).2 = _
  rw [tubeMap_fst, tubeMap_snd, mul_comm, unitOf_circle_mul' _ (mul_ne_zero (by norm_num) hω),
    unitOf_three_mul hω]
  simp only [linearTorusMap, ConeFilling.chartMatrix, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  rw [mul_zpow, ← zpow_neg_one, ← zpow_mul, ← Circle.exp_zsmul, ← Circle.exp_zsmul]
  have hdet := c.det_eq
  have h : (-c.q) • (2 * Real.pi * c.a * p 2) + c.b • (2 * Real.pi * c.p * p 2) =
      2 * Real.pi * p 2 := by
    simp only [zsmul_eq_mul, Int.cast_neg]
    have : ((c.p : ℤ) : ℝ) * c.b - c.a * c.q = 1 := by exact_mod_cast hdet
    push_cast at this ⊢
    linear_combination (2 * Real.pi * p 2) * this
  rw [mul_assoc, mul_comm (unitOf _ ^ (-c.q)), ← mul_assoc, ← Circle.exp_add, h, mul_neg_one]

end ConeShape

namespace ConeShape.FoldData

variable {σ : ConeShape} (D : σ.FoldData) (c : ConeFilling)

def baseMap (p : ModelCoordinates) : PlaneLift.{u} × Circle :=
  (ULift.up (D.f (logPoint p)),
    Circle.exp (2 * Real.pi * p 2) * (σ.foldPhase c.q (logPoint p))⁻¹)

def liftMap (p : ModelCoordinates) : PlaneLift.{u} × Circle := c.coneLift (D.baseMap c p)

def totalMap (p : ModelCoordinates) : PlaneLift.{u} × Circle :=
  if (logPoint p : ℂ) = σ.vertexOne then σ.tubeMap c p else D.liftMap c p

theorem baseMap_fst (p : ModelCoordinates) : (D.baseMap.{u} c p).1.down = D.f (logPoint p) := rfl

theorem baseMap_snd (p : ModelCoordinates) :
    (D.baseMap.{u} c p).2 = Circle.exp (2 * Real.pi * p 2) * (σ.foldPhase c.q (logPoint p))⁻¹ :=
  rfl

theorem tubeMap_eq_liftMap {p : ModelCoordinates} (hv : (logPoint p : ℂ) ≠ σ.vertexOne)
    (hfar : (logPoint p : ℂ) ∈ σ.foldFar)
    (hf : D.f (logPoint p) = σ.coneApexOne c.p (logPoint p)) :
    σ.tubeMap.{u} c p = D.liftMap c p := by
  have hω := σ.coneDisc_ne_zero_of_ne (logPoint_im_pos p) hv
  have hne : (σ.tubeMap.{u} c p).1.down ≠ 0 := by
    rw [tubeMap_fst]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hω) (Circle.coe_ne_zero _)
  rw [liftMap, ← c.coneLift_coneChart (σ.tubeMap c p) hne, σ.coneChart_tubeMap c hv]
  congr 1
  refine Prod.ext (ULift.ext ?_) ?_
  · exact hf.symm
  · change _ = Circle.exp (2 * Real.pi * p 2) * (σ.foldPhase c.q (logPoint p))⁻¹
    rw [σ.foldPhase_eq_unitOf c.q (logPoint_im_pos p) hv hfar]

theorem conePoint_liftMap {p : ModelCoordinates} (hf : D.f (logPoint p) ≠ 3 / 2) :
    c.conePoint (D.liftMap.{u} c p) = D.f (logPoint p) := by
  rw [liftMap, c.conePoint_coneLift _ (by rw [baseMap_fst]; push_cast; exact hf)]
  rfl

def conjMap (x : PlaneLift.{u} × Circle) : PlaneLift.{u} × Circle :=
  (ULift.up (conj x.1.down), x.2⁻¹)

theorem conjMap_conjMap (x : PlaneLift.{u} × Circle) : conjMap (conjMap x) = x := by
  simp [conjMap]

theorem conePoint_conjMap (x : PlaneLift.{u} × Circle) :
    c.conePoint (conjMap x) = conj (c.conePoint x) := by
  simp only [ConeFilling.conePoint, conjMap, map_add, map_div₀, map_pow, map_ofNat,
    Complex.conj_ofReal, map_mul]
  rw [← Circle.coe_inv_eq_conj, inv_zpow]

theorem contMDiff_conjMap : ContMDiff PlaneCircleModel PlaneCircleModel ∞ conjMap.{u} := by
  have h2 : ContMDiff PlaneCircleModel (𝓡 1) ∞ (fun x : PlaneLift.{u} × Circle => x.2⁻¹) :=
    (contMDiff_snd : ContMDiff PlaneCircleModel (𝓡 1) ∞
      (Prod.snd : PlaneLift.{u} × Circle → Circle)).inv
  exact (contMDiff_planeLift_up.comp (Complex.conjCLE.contDiff.contMDiff.comp
    (contMDiff_planeLift_down.comp contMDiff_fst))).prodMk h2

def flipMap (p : ModelCoordinates) : ModelCoordinates := !₂[-p 0, p 1, -p 2]

@[simp] theorem flipMap_zero (p : ModelCoordinates) : flipMap p 0 = -p 0 := by simp [flipMap]

@[simp] theorem flipMap_one (p : ModelCoordinates) : flipMap p 1 = p 1 := by simp [flipMap]

@[simp] theorem flipMap_two (p : ModelCoordinates) : flipMap p 2 = -p 2 := by simp [flipMap]

theorem flipMap_flipMap (p : ModelCoordinates) : flipMap (flipMap p) = p := by
  ext i
  fin_cases i <;> simp

theorem coe_logPoint_flipMap (p : ModelCoordinates) :
    (logPoint (flipMap p) : ℂ) = σ.refl 0 (logPoint p) := by
  rw [coe_logPoint', coe_logPoint']
  apply Complex.ext <;> simp [ConeShape.refl]

theorem contDiff_flipMap : ContDiff ℝ ∞ flipMap := by
  have hc (j : Fin 3) : ContDiff ℝ ∞ (fun q : ModelCoordinates =>
      (PiLp.proj 2 (fun _ : Fin 3 => ℝ) j : ModelCoordinates →L[ℝ] ℝ) q) :=
    (PiLp.proj 2 (fun _ : Fin 3 => ℝ) j : ModelCoordinates →L[ℝ] ℝ).contDiff
  apply contDiff_euclidean.2
  intro i
  fin_cases i
  · exact (hc 0).neg
  · exact hc 1
  · exact (hc 2).neg

def mirrorMap (p : ModelCoordinates) : PlaneLift.{u} × Circle :=
  if p 0 < 0 then conjMap (D.totalMap c (flipMap p)) else D.totalMap c p

end ConeShape.FoldData

end GC.Seifert
