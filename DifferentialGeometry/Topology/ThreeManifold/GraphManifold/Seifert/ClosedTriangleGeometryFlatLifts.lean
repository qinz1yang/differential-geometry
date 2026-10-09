import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryFlatCover
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryPhase
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryLift
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryOuterSeam

/-!
# The model lifts of a flat closed triangle fold and their apex identities

Lane B3 (design `docs/geometrization/handoffs/20261004-design-b3-closed-triangle-assembly.md`,
§2.3–§2.4, with review 27). A `FlatDatum` collects a flat triangle `σ`, a fold datum `D` on it, the
twists and Bézout columns `(qⱼ, aⱼ, bⱼ)` of the three cones (cone `3` at the outer hole), a
connection model `m` with flat base (connection curvature `c`) and a nonzero signed fibre step `ℓ`
with the closing equation `-c (v₁ × v₂) = ℓ e`. On `ModelCoordinates` (`z = planeOf x`, `t = x 2`):
* the base lift `liftP x = (f z, e(t/ℓ) e^{-iΘ(z, f z)})` on the triangle side and its mirror
  `liftM = conjPair ∘ liftP ∘ reflectMap c₀`, `c₀ = ℓ (k₁ + k₂)`;
* the tube coordinates `tubeOne x = (rotOne z e(a₁ s₁), e(p₁ s₁))`, `tubeTwo`, and
  `tubeThree x = (e^{iπ/p₃} z e(a₃ s₃), e(p₃ s₃))`, with `sⱼ = t/ℓ + βⱼ z` and the smooth fibre
  shifts `β₁ = -ψ₁/ℓ - (k₂ φ_{-3/2}(apexOne) - π e)/2π`, `β₂ = -ψ₂/ℓ - k₁ φ_{3/2}(apexTwo)/2π`,
  `β₃ = k₃ + e/2`.
In the good sector of each vertex the base lift is the seam model of the tube coordinates
(`liftP_eq_seamFwd_tubeOne`, `liftP_eq_seamFwd_tubeTwo`, `liftP_eq_outerFwd_tubeThree`).
-/

set_option autoImplicit false

noncomputable section
open Set Complex
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Topology ComplexConjugate ContDiff Manifold

namespace GC.Seifert

namespace ClosedTriangle

open TwoConeFold

structure FlatDatum where
  σ : EuclidShape
  D : σ.toCompactShape.FoldData
  q₁ : ℤ
  q₂ : ℤ
  q₃ : ℤ
  a₁ : ℤ
  a₂ : ℤ
  a₃ : ℤ
  b₁ : ℤ
  b₂ : ℤ
  b₃ : ℤ
  bez₁ : (σ.p₁ : ℤ) * b₁ - a₁ * q₁ = 1
  bez₂ : (σ.p₂ : ℤ) * b₂ - a₂ * q₂ = 1
  bez₃ : (σ.p₃ : ℤ) * b₃ - a₃ * q₃ = 1
  m : ConnectionModel
  base_flat : m.baseCurvature = 0
  ℓ : ℝ
  ℓ_ne : ℓ ≠ 0
  closing : -m.connectionCurvature * planeCrossC σ.vertexOne σ.vertexTwo =
    ℓ * -((q₁ : ℝ) / σ.p₁ + (q₂ : ℝ) / σ.p₂ + (q₃ : ℝ) / σ.p₃)

section Reflect

def reflLinear : ModelCoordinates →ₗ[ℝ] ModelCoordinates where
  toFun p := !₂[p 0, -p 1, -p 2]
  map_add' p q := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' c p := by
    ext i
    fin_cases i <;> simp

def reflCLM : ModelCoordinates →L[ℝ] ModelCoordinates := LinearMap.toContinuousLinearMap reflLinear

theorem reflCLM_apply (p : ModelCoordinates) : reflCLM p = !₂[p 0, -p 1, -p 2] := rfl

def reflectMap (c : ℝ) (p : ModelCoordinates) : ModelCoordinates := reflCLM p + !₂[0, 0, c]

theorem reflectMap_zero (c : ℝ) (p : ModelCoordinates) : reflectMap c p 0 = p 0 := by
  simp [reflectMap, reflCLM_apply]

theorem reflectMap_one (c : ℝ) (p : ModelCoordinates) : reflectMap c p 1 = -p 1 := by
  simp [reflectMap, reflCLM_apply]

theorem reflectMap_two (c : ℝ) (p : ModelCoordinates) : reflectMap c p 2 = c - p 2 := by
  simp [reflectMap, reflCLM_apply]
  ring

theorem planeOf_reflectMap (c : ℝ) (p : ModelCoordinates) :
    planeOf (reflectMap c p) = conj (planeOf p) := by
  apply Complex.ext <;> simp [reflectMap_zero, reflectMap_one]

theorem reflectMap_reflectMap (c : ℝ) (p : ModelCoordinates) :
    reflectMap c (reflectMap c p) = p := by
  apply modelCoordinates_ext
  · rw [planeOf_reflectMap, planeOf_reflectMap, Complex.conj_conj]
  · rw [reflectMap_two, reflectMap_two]
    ring

theorem contDiff_reflectMap (c : ℝ) : ContDiff ℝ ∞ (reflectMap c) :=
  reflCLM.contDiff.add contDiff_const

def reflectDiffeo (c : ℝ) : ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates where
  toFun := reflectMap c
  invFun := reflectMap c
  left_inv := reflectMap_reflectMap c
  right_inv := reflectMap_reflectMap c
  contMDiff_toFun := (contDiff_reflectMap c).contMDiff
  contMDiff_invFun := (contDiff_reflectMap c).contMDiff

theorem reflectDiffeo_apply (c : ℝ) (p : ModelCoordinates) : reflectDiffeo c p = reflectMap c p :=
  rfl

def conjPairDiffeo : (ℂ × Circle) ≃ₘ⟮PlaneCircleModel, PlaneCircleModel⟯ (ℂ × Circle) where
  toFun := conjPair
  invFun := conjPair
  left_inv := conjPair_conjPair
  right_inv := conjPair_conjPair
  contMDiff_toFun := (Complex.conjCLE.contDiff.contMDiff.comp contMDiff_fst).prodMk
    (contMDiff_snd.inv)
  contMDiff_invFun := (Complex.conjCLE.contDiff.contMDiff.comp contMDiff_fst).prodMk
    (contMDiff_snd.inv)

end Reflect

theorem outerFwd_conjPair (P : ℕ) (p q a b : ℤ) (y : ℂ × Circle) :
    outerFwd P p q a b (conjPair y) = conjPair (outerFwd P p q a b y) := by
  have h1 : unitOf (conj y.1) ^ (-p) * (y.2⁻¹) ^ a = (unitOf y.1 ^ (-p) * y.2 ^ a)⁻¹ := by
    rw [unitOf_conj'']
    simp only [inv_zpow, mul_inv]
  have h2 : unitOf (conj y.1) ^ (-q) * (y.2⁻¹) ^ b = (unitOf y.1 ^ (-q) * y.2 ^ b)⁻¹ := by
    rw [unitOf_conj'']
    simp only [inv_zpow, mul_inv]
  apply Prod.ext
  · change ((((7 / 2 - ‖conj y.1‖ ^ P / 2 : ℝ)) : ℂ) *
      ((unitOf (conj y.1) ^ (-p) * (y.2⁻¹) ^ a : Circle) : ℂ)) =
        conj ((((7 / 2 - ‖y.1‖ ^ P / 2 : ℝ)) : ℂ) * ((unitOf y.1 ^ (-p) * y.2 ^ a : Circle) : ℂ))
    rw [h1, Circle.coe_inv_eq_conj, norm_conj, map_mul, conj_ofReal]
  · change unitOf (conj y.1) ^ (-q) * (y.2⁻¹) ^ b = (unitOf y.1 ^ (-q) * y.2 ^ b)⁻¹
    exact h2

section Pieces

variable {σ : EuclidShape} (D : σ.toCompactShape.FoldData)

theorem im_pos_of_main_not_patchZero {z : ℂ} (hm : z ∈ mainSet D) (hz : z ∉ patchZero D) :
    0 < z.im := by
  have hk := kap_pos D
  rcases hm with ((h | h) | h) | h
  · exact h 0
  · exact absurd h hz
  · have := h.2.1
    change kap D < z.im at this
    linarith
  · have := h.2.1
    change kap D < z.im at this
    linarith

theorem conj_mem_patchZero {z : ℂ} (hz : z ∈ patchZero D) : conj z ∈ patchZero D :=
  refl_mem_patchZero D hz

theorem mem_patchZero_of_main_conj {z : ℂ} (hm : z ∈ mainSet D) (hm' : conj z ∈ mainSet D) :
    z ∈ patchZero D := by
  by_contra hz
  have h1 := im_pos_of_main_not_patchZero D hm hz
  have h2 : conj z ∉ patchZero D := fun h => hz (by
    have := conj_mem_patchZero D h
    rwa [Complex.conj_conj] at this)
  have h3 := im_pos_of_main_not_patchZero D hm' h2
  rw [conj_im] at h3
  linarith

theorem not_mem_discOneMirror_of_main {z : ℂ} (hm : z ∈ mainSet D) : z ∉ discOneMirror D := by
  intro hd
  have him := im_neg_of_mem_discOneMirror D hd
  have hρ := rhoZero_pos (σ := σ)
  have hz : z ∈ patchZero D := by
    by_contra hz
    have := im_pos_of_main_not_patchZero D hm hz
    linarith
  have hd' := (mem_discOneMirror_iff D).1 hd
  have hre := re_f_of_mem_discOne D hd'
  have hfl : D.f (conj z) = conj (D.f z) := f_refl' D 0 hz.1
  rw [hfl, conj_re] at hre
  linarith [hz.2.2.2.2.2.1]

theorem not_mem_discOne_of_conj_main {z : ℂ} (hm : conj z ∈ mainSet D) : z ∉ discOne D := by
  intro hd
  apply not_mem_discOneMirror_of_main D hm
  rw [mem_discOneMirror_iff, Complex.conj_conj]
  exact hd

theorem conj_mem_discTwo {z : ℂ} (hd : z ∈ discTwo D) : conj z ∈ discTwo D := by
  change ‖conj z - σ.vertexTwo‖ < radTwo D
  rw [← σ.conj_vertexTwo, ← map_sub, Complex.norm_conj]
  exact hd

theorem conj_mem_discThree {z : ℂ} (hd : z ∈ discThree D) : conj z ∈ discThree D := by
  change ‖conj z‖ < radThree D
  rw [Complex.norm_conj]
  exact hd

end Pieces

namespace FlatDatum

variable (K : FlatDatum)

def c : ℝ := K.m.connectionCurvature

def k₁ : ℝ := (K.q₁ : ℝ) / K.σ.p₁

def k₂ : ℝ := (K.q₂ : ℝ) / K.σ.p₂

def k₃ : ℝ := (K.q₃ : ℝ) / K.σ.p₃

def phase : PhaseData := ⟨K.k₁, K.k₂, K.k₃, K.c, K.ℓ, K.σ.vertexOne, K.σ.vertexTwo⟩

def c₀ : ℝ := K.ℓ * (K.k₁ + K.k₂)

def psiC (z : ℂ) : Circle := Circle.exp (-(K.phase.theta z (K.D.f z)))

def liftP (x : ModelCoordinates) : ℂ × Circle :=
  (K.D.f (planeOf x), eC (x 2 / K.ℓ) * K.psiC (planeOf x))

def liftM (x : ModelCoordinates) : ℂ × Circle := conjPair (K.liftP (reflectMap K.c₀ x))

def betaOne (z : ℂ) : ℝ :=
  -(K.phase.psi K.σ.vertexOne z / K.ℓ) -
    (K.k₂ * phaseArg (-(3 / 2)) (K.σ.apexOne z) - Real.pi * K.phase.e) / (2 * Real.pi)

def betaTwo (z : ℂ) : ℝ :=
  -(K.phase.psi K.σ.vertexTwo z / K.ℓ) - K.k₁ * phaseArg (3 / 2) (K.σ.apexTwo z) / (2 * Real.pi)

def betaThree : ℝ := K.k₃ + K.phase.e / 2

def sOne (x : ModelCoordinates) : ℝ := x 2 / K.ℓ + K.betaOne (planeOf x)

def sTwo (x : ModelCoordinates) : ℝ := x 2 / K.ℓ + K.betaTwo (planeOf x)

def sThree (x : ModelCoordinates) : ℝ := x 2 / K.ℓ + K.betaThree

def tubeOne (x : ModelCoordinates) : ℂ × Circle :=
  (K.σ.rotOne (planeOf x) * (eC (K.a₁ * K.sOne x) : ℂ), eC (K.σ.p₁ * K.sOne x))

def tubeTwo (x : ModelCoordinates) : ℂ × Circle :=
  (K.σ.rotTwo (planeOf x) * (eC (K.a₂ * K.sTwo x) : ℂ), eC (K.σ.p₂ * K.sTwo x))

def tubeThree (x : ModelCoordinates) : ℂ × Circle :=
  ((Circle.exp (Real.pi / K.σ.p₃) : ℂ) * planeOf x * (eC (K.a₃ * K.sThree x) : ℂ),
    eC (K.σ.p₃ * K.sThree x))

theorem p₁_pos : 0 < K.σ.p₁ := by have := K.σ.two_le_p₁; omega

theorem p₂_pos : 0 < K.σ.p₂ := by have := K.σ.two_le_p₂; omega

theorem p₃_pos : 0 < K.σ.p₃ := by have := K.σ.two_le_p₃; omega

theorem k₁_mul : K.k₁ * K.σ.p₁ = K.q₁ := by
  rw [k₁, div_mul_cancel₀ _ (by exact_mod_cast K.p₁_pos.ne')]

theorem k₂_mul : K.k₂ * K.σ.p₂ = K.q₂ := by
  rw [k₂, div_mul_cancel₀ _ (by exact_mod_cast K.p₂_pos.ne')]

theorem k₃_mul : K.k₃ * K.σ.p₃ = K.q₃ := by
  rw [k₃, div_mul_cancel₀ _ (by exact_mod_cast K.p₃_pos.ne')]

theorem phase_e : K.phase.e = -(K.k₁ + K.k₂ + K.k₃) := rfl

@[simp] theorem phase_k₁ : K.phase.k₁ = K.k₁ := rfl

@[simp] theorem phase_k₂ : K.phase.k₂ = K.k₂ := rfl

@[simp] theorem phase_k₃ : K.phase.k₃ = K.k₃ := rfl

@[simp] theorem phase_c : K.phase.c = K.c := rfl

@[simp] theorem phase_ℓ : K.phase.ℓ = K.ℓ := rfl

@[simp] theorem phase_v₁ : K.phase.v₁ = K.σ.vertexOne := rfl

@[simp] theorem phase_v₂ : K.phase.v₂ = K.σ.vertexTwo := rfl

theorem phase_closing : -K.phase.c * planeCrossC K.phase.v₁ K.phase.v₂ = K.phase.ℓ * K.phase.e :=
  K.closing

theorem circle_exp_arg_zpow {w : ℂ} (hw : w ≠ 0) (n : ℤ) :
    unitOf w ^ n = Circle.exp (n * arg w) := by
  rw [unitOf_eq_exp_arg hw, Circle.exp_intCast_mul]

theorem norm_rotOne_pow_le {z : ℂ} (hd : z ∈ discOne K.D) : ‖K.σ.rotOne z‖ ^ K.σ.p₁ ≤ 1 := by
  rw [norm_rotOne]
  exact pow_le_one₀ (norm_nonneg _) ((le_of_lt hd).trans (by linarith [radOne_le_half K.D]))

theorem norm_rotTwo_pow_le {z : ℂ} (hd : z ∈ discTwo K.D) : ‖K.σ.rotTwo z‖ ^ K.σ.p₂ ≤ 1 := by
  rw [norm_rotTwo]
  exact pow_le_one₀ (norm_nonneg _) ((le_of_lt hd).trans (by linarith [radTwo_le_half K.D]))

theorem mul_arg_bounds {θ : ℝ} {p : ℕ} (hθ : θ * p = Real.pi) {w : ℂ}
    (h1 : -(θ / 2) < arg w) (h2 : arg w < 3 * θ / 2) :
    -(Real.pi / 2) < p * arg w ∧ p * arg w < 3 * Real.pi / 2 := by
  have hp : (0 : ℝ) < p := by
    rcases (Nat.cast_nonneg p : (0 : ℝ) ≤ p).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hθ
      exact absurd hθ.symm Real.pi_ne_zero
  have e1 := mul_lt_mul_of_pos_left h1 hp
  have e2 := mul_lt_mul_of_pos_left h2 hp
  constructor <;> nlinarith

theorem liftP_eq_seamFwd_tubeOne {x : ModelCoordinates} (hd : planeOf x ∈ discOne K.D)
    (hs : K.σ.rotOne (planeOf x) ≠ 0 ∧ -(K.σ.θ₁ / 2) < arg (K.σ.rotOne (planeOf x)) ∧
      arg (K.σ.rotOne (planeOf x)) < 3 * K.σ.θ₁ / 2) :
    K.liftP x = seamFwd ((3 / 2 : ℝ) : ℂ) K.σ.p₁ K.σ.p₁ K.q₁ K.a₁ K.b₁ (K.tubeOne x) := by
  obtain ⟨hne, h1, h2⟩ := hs
  obtain ⟨b1, b2⟩ := mul_arg_bounds K.σ.θ₁_mul h1 h2
  set z := planeOf x with hz
  set η := K.σ.rotOne z with hη
  have hap := seamFwd_apex (c := ((3 / 2 : ℝ) : ℂ)) (P := K.σ.p₁) (p := K.σ.p₁) (q := K.q₁)
    (a := K.a₁) (b := K.b₁) K.bez₁ rfl η hne (K.sOne x)
  have hfz : K.D.f z = 3 / 2 + η ^ K.σ.p₁ / 2 := by
    rw [(f_of_mem_discOne K.D hd).2]
    rfl
  have hθ := K.phase.theta_vertexOne (z := z) hfz hne (K.norm_rotOne_pow_le hd) b1 b2.le
  unfold tubeOne
  change _ = seamFwd ((3 / 2 : ℝ) : ℂ) K.σ.p₁ K.σ.p₁ K.q₁ K.a₁ K.b₁
    (η * (Circle.exp (2 * Real.pi * (K.a₁ * K.sOne x)) : ℂ),
      Circle.exp (2 * Real.pi * (K.σ.p₁ * K.sOne x)))
  rw [hap]
  unfold liftP
  rw [← hz]
  congr 1
  · rw [hfz]
    push_cast
    ring
  have hapex : K.σ.apexOne z = 3 / 2 + η ^ K.σ.p₁ / 2 := rfl
  rw [psiC, hθ, hfz, circle_exp_arg_zpow hne, eC, ← Circle.exp_add, ← Circle.exp_add]
  congr 1
  have hk := K.k₁_mul
  have hℓ := K.ℓ_ne
  simp only [sOne, betaOne, ← hz, hapex, phase_k₁, phase_k₂, phase_ℓ, phase_v₁]
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  push_cast
  field_simp
  linear_combination (-(K.ℓ * arg η)) * hk

theorem liftP_eq_seamFwd_tubeTwo {x : ModelCoordinates} (hd : planeOf x ∈ discTwo K.D)
    (hs : K.σ.rotTwo (planeOf x) ≠ 0 ∧ -(K.σ.θ₂ / 2) < arg (K.σ.rotTwo (planeOf x)) ∧
      arg (K.σ.rotTwo (planeOf x)) < 3 * K.σ.θ₂ / 2) :
    K.liftP x = seamFwd ((-(3 / 2) : ℝ) : ℂ) K.σ.p₂ K.σ.p₂ K.q₂ K.a₂ K.b₂ (K.tubeTwo x) := by
  obtain ⟨hne, h1, h2⟩ := hs
  obtain ⟨b1, b2⟩ := mul_arg_bounds K.σ.θ₂_mul h1 h2
  set z := planeOf x with hz
  set η := K.σ.rotTwo z with hη
  have hap := seamFwd_apex (c := ((-(3 / 2) : ℝ) : ℂ)) (P := K.σ.p₂) (p := K.σ.p₂) (q := K.q₂)
    (a := K.a₂) (b := K.b₂) K.bez₂ rfl η hne (K.sTwo x)
  have hfz : K.D.f z = -(3 / 2) + η ^ K.σ.p₂ / 2 := by
    rw [(f_of_mem_discTwo K.D hd).2]
    rfl
  have hθ := K.phase.theta_vertexTwo (z := z) hfz hne (K.norm_rotTwo_pow_le hd) b1 b2.le
  unfold tubeTwo
  change _ = seamFwd ((-(3 / 2) : ℝ) : ℂ) K.σ.p₂ K.σ.p₂ K.q₂ K.a₂ K.b₂
    (η * (Circle.exp (2 * Real.pi * (K.a₂ * K.sTwo x)) : ℂ),
      Circle.exp (2 * Real.pi * (K.σ.p₂ * K.sTwo x)))
  rw [hap]
  unfold liftP
  rw [← hz]
  congr 1
  · rw [hfz]
    push_cast
    ring
  have hapex : K.σ.apexTwo z = -(3 / 2) + η ^ K.σ.p₂ / 2 := rfl
  rw [psiC, hθ, hfz, circle_exp_arg_zpow hne, eC, ← Circle.exp_add, ← Circle.exp_add]
  congr 1
  have hk := K.k₂_mul
  have hℓ := K.ℓ_ne
  simp only [sTwo, betaTwo, ← hz, hapex, phase_k₁, phase_k₂, phase_ℓ, phase_v₂]
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  push_cast
  field_simp
  linear_combination (-(K.ℓ * arg η)) * hk

theorem normSq_f_of_mem_discThree {z : ℂ} (hd : z ∈ discThree K.D) (h0 : z ≠ 0) :
    9 ≤ normSq (K.D.f z) := by
  have h := norm_f_of_mem_discThree K.D hd h0
  rw [normSq_eq_norm_sq]
  nlinarith

theorem liftP_eq_outerFwd_tubeThree {x : ModelCoordinates} (hd : planeOf x ∈ discThree K.D)
    (hs : planeOf x ≠ 0 ∧ -(K.σ.θ₃ / 2) < arg (planeOf x) ∧ arg (planeOf x) < 3 * K.σ.θ₃ / 2) :
    K.liftP x = outerFwd K.σ.p₃ K.σ.p₃ K.q₃ K.a₃ K.b₃ (K.tubeThree x) := by
  obtain ⟨hne, h1, h2⟩ := hs
  obtain ⟨b1, b2⟩ := mul_arg_bounds K.σ.θ₃_mul h1 h2
  set z := planeOf x with hz
  have hap := outerFwd_apex (P := K.σ.p₃) (p := K.σ.p₃) (q := K.q₃) (a := K.a₃) (b := K.b₃)
    K.bez₃ K.p₃_pos.ne' rfl z hne (K.sThree x)
  have hfz : K.D.f z = compactOuterGerm K.σ.p₃ z := (f_of_mem_discThree K.D hd hne).2
  have hn9 := K.normSq_f_of_mem_discThree hd hne
  have hθ := K.phase.theta_outer (z := z) hn9
  have hzp : ‖z‖ ^ K.σ.p₃ < 7 := by
    have : ‖z‖ ^ K.σ.p₃ ≤ 1 := pow_le_one₀ (norm_nonneg _)
      ((le_of_lt hd).trans (by linarith [radThree_le_half K.D]))
    linarith
  have hφ := phaseArg_compactOuterGerm hne hzp b1.le b2
  unfold tubeThree
  change _ = outerFwd K.σ.p₃ K.σ.p₃ K.q₃ K.a₃ K.b₃
    ((Circle.exp (Real.pi / K.σ.p₃) : ℂ) * z *
      (Circle.exp (2 * Real.pi * (K.a₃ * K.sThree x)) : ℂ),
      Circle.exp (2 * Real.pi * (K.σ.p₃ * K.sThree x)))
  rw [hap]
  unfold liftP
  rw [← hz]
  congr 1
  rw [psiC, hθ, hfz, hφ, circle_exp_arg_zpow hne, eC, ← Circle.exp_add, ← Circle.exp_add,
    ← Circle.exp_add]
  congr 1
  have hk := K.k₃_mul
  have hℓ := K.ℓ_ne
  have hp3 : (K.σ.p₃ : ℝ) ≠ 0 := by exact_mod_cast K.p₃_pos.ne'
  simp only [sThree, betaThree, phase_k₃, phase_e]
  push_cast
  field_simp
  linear_combination (-(Real.pi * K.ℓ) - K.σ.p₃ * K.ℓ * arg z) * hk

theorem planeCrossC_eq_im (v w : ℂ) : planeCrossC v w = (conj v * w).im := by
  simp only [planeCrossC, mul_im, conj_re, conj_im]
  ring

theorem psi_vertexTwo_conj (z : ℂ) :
    K.phase.psi K.σ.vertexTwo (conj z) = -K.phase.psi K.σ.vertexTwo z := by
  simp only [PhaseData.psi, planeCrossC_eq_im, K.σ.conj_vertexTwo]
  have : K.σ.vertexTwo * conj z = conj (K.σ.vertexTwo * z) := by
    rw [map_mul, K.σ.conj_vertexTwo]
  rw [this, conj_im]
  ring

theorem psi_vertexOne_refl_one (z : ℂ) :
    K.phase.psi K.σ.vertexOne (K.σ.refl 1 z) = -K.phase.psi K.σ.vertexOne z := by
  simp only [PhaseData.psi, planeCrossC_eq_im]
  have : conj K.σ.vertexOne * K.σ.refl 1 z = conj (conj K.σ.vertexOne * z) := by
    change conj K.σ.vertexOne * (exp (2 * (K.σ.θ₃ : ℂ) * I) * conj z) = _
    rw [map_mul, Complex.conj_conj, K.σ.conj_vertexOne]
    have e : exp (-(2 * (K.σ.θ₃ : ℂ) * I)) * exp (2 * (K.σ.θ₃ : ℂ) * I) = 1 := by
      rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    linear_combination (K.σ.vertexOne * conj z) * e
  rw [this, conj_im]
  ring

theorem liftM_eq_liftP {x : ModelCoordinates} (hV : planeOf x ∈ K.D.V 0)
    (hre : (K.D.f (planeOf x)).re < -(3 / 2)) : K.liftM x = K.liftP x := by
  set z := planeOf x with hz
  have hfl : K.D.f (conj z) = conj (K.D.f z) := f_refl' K.D 0 hV
  have hθ := K.phase.theta_wallZero (z := z) (z' := conj z) hre (K.psi_vertexTwo_conj z)
  unfold liftM liftP conjPair
  rw [planeOf_reflectMap, ← hz, hfl, Complex.conj_conj, reflectMap_two]
  congr 1
  rw [psiC, hfl, mul_inv, ← Circle.exp_neg, neg_neg, eC, eC, ← Circle.exp_neg, ← Circle.exp_add,
    psiC, ← Circle.exp_add]
  congr 1
  have hℓ := K.ℓ_ne
  simp only [c₀, phase_k₁, phase_k₂] at hθ ⊢
  field_simp
  linear_combination K.ℓ * hθ

theorem re_apexTwo_lt {z : ℂ} (hd : z ∈ discTwo K.D) : (K.σ.apexTwo z).re < 3 / 2 := by
  have := re_f_of_mem_discTwo K.D hd
  rw [(f_of_mem_discTwo K.D hd).2] at this
  linarith

theorem re_apexOne_gt {z : ℂ} (hd : z ∈ discOne K.D) : -(3 / 2) < (K.σ.apexOne z).re := by
  have := re_f_of_mem_discOne K.D hd
  rw [(f_of_mem_discOne K.D hd).2] at this
  linarith

theorem betaTwo_conj {z : ℂ} (hd : z ∈ discTwo K.D) :
    K.betaTwo (conj z) = -K.betaTwo z - K.k₁ := by
  have ha : K.σ.apexTwo (conj z) = conj (K.σ.apexTwo z) := K.σ.apexTwo_refl_zero z
  simp only [betaTwo, ha, phaseArg_conj_of_gt (K.re_apexTwo_lt hd), K.psi_vertexTwo_conj]
  have hℓ := K.ℓ_ne
  field_simp
  ring

theorem betaOne_refl_one {z : ℂ} (hd : z ∈ discOne K.D) :
    K.betaOne (K.σ.refl 1 z) = -K.betaOne z + K.phase.e := by
  have ha : K.σ.apexOne (K.σ.refl 1 z) = conj (K.σ.apexOne z) := K.σ.apexOne_refl_one z
  simp only [betaOne, ha, phaseArg_conj_of_lt (K.re_apexOne_gt hd), K.psi_vertexOne_refl_one]
  have hℓ := K.ℓ_ne
  field_simp
  ring

theorem p_inv_eq {p : ℕ} (hp : 0 < p) {θ : ℝ} (hθ : θ * p = Real.pi) : θ = Real.pi / p := by
  rw [← hθ, mul_div_cancel_right₀ _ (by exact_mod_cast hp.ne')]

theorem conjPair_tubeTwo_reflect {x : ModelCoordinates} (hd : planeOf x ∈ discTwo K.D) :
    conjPair (K.tubeTwo (reflectMap K.c₀ x)) = K.tubeTwo x := by
  set z := planeOf x with hz
  have hβ := K.betaTwo_conj hd
  have hk := K.k₂_mul
  have hℓ := K.ℓ_ne
  have hθp := p_inv_eq K.p₂_pos K.σ.θ₂_mul
  have hsum : K.sTwo (reflectMap K.c₀ x) = -K.sTwo x + K.k₂ := by
    simp only [sTwo, planeOf_reflectMap, reflectMap_two, ← hz, hβ, c₀]
    field_simp
    ring
  unfold tubeTwo conjPair
  rw [hsum, planeOf_reflectMap, ← hz]
  apply Prod.ext
  · change conj (K.σ.rotTwo (conj z) * (eC (K.a₂ * (-K.sTwo x + K.k₂)) : ℂ)) =
      K.σ.rotTwo z * (eC (K.a₂ * K.sTwo x) : ℂ)
    have hr : K.σ.rotTwo (conj z) = exp (2 * (K.σ.θ₂ : ℂ) * I) * conj (K.σ.rotTwo z) :=
      K.σ.rotTwo_refl_zero z
    have e1 : conj (exp (2 * (K.σ.θ₂ : ℂ) * I)) = (Circle.exp (-(2 * K.σ.θ₂)) : ℂ) := by
      rw [Circle.coe_exp, ← Complex.exp_conj]
      congr 1
      rw [map_mul, map_mul, conj_I, conj_ofReal, map_ofNat]
      push_cast
      ring
    rw [hr, map_mul, map_mul, Complex.conj_conj, e1, ← Circle.coe_inv_eq_conj, ← eC_neg]
    have key : Circle.exp (-(2 * K.σ.θ₂)) * eC (-(K.a₂ * (-K.sTwo x + K.k₂))) =
        eC (K.a₂ * K.sTwo x) := by
      rw [eC, eC, ← Circle.exp_add]
      have hb : ((K.σ.p₂ : ℝ) * K.b₂ - K.a₂ * K.q₂) = 1 := by exact_mod_cast K.bez₂
      have : -(2 * K.σ.θ₂) + 2 * Real.pi * -(K.a₂ * (-K.sTwo x + K.k₂)) =
          2 * Real.pi * (K.a₂ * K.sTwo x) + ((-K.b₂ : ℤ) : ℝ) * (2 * Real.pi) := by
        rw [hθp, k₂]
        have hp0 : (K.σ.p₂ : ℝ) ≠ 0 := by exact_mod_cast K.p₂_pos.ne'
        push_cast
        field_simp
        linear_combination hb
      rw [this, Circle.exp_add, Circle.exp_int_mul_two_pi, mul_one]
    have := congrArg (fun w : Circle => (w : ℂ) * K.σ.rotTwo z) key
    simp only [Circle.coe_mul] at this
    linear_combination this
  · change (eC (K.σ.p₂ * (-K.sTwo x + K.k₂)))⁻¹ = eC (K.σ.p₂ * K.sTwo x)
    rw [← eC_neg]
    have : -(K.σ.p₂ * (-K.sTwo x + K.k₂)) = K.σ.p₂ * K.sTwo x + ((-K.q₂ : ℤ) : ℝ) := by
      push_cast
      linear_combination -hk
    rw [this, eC_add, eC_int, mul_one]

theorem conjPair_tubeThree_reflect (x : ModelCoordinates) :
    conjPair (K.tubeThree (reflectMap K.c₀ x)) = K.tubeThree x := by
  have hk := K.k₃_mul
  have hℓ := K.ℓ_ne
  have hsum : K.sThree (reflectMap K.c₀ x) = -K.sThree x + K.k₃ := by
    simp only [sThree, betaThree, reflectMap_two, c₀, phase_e]
    field_simp
    ring
  unfold tubeThree conjPair
  rw [hsum, planeOf_reflectMap]
  apply Prod.ext
  · change conj ((Circle.exp (Real.pi / K.σ.p₃) : ℂ) * conj (planeOf x) *
      (eC (K.a₃ * (-K.sThree x + K.k₃)) : ℂ)) =
      (Circle.exp (Real.pi / K.σ.p₃) : ℂ) * planeOf x * (eC (K.a₃ * K.sThree x) : ℂ)
    rw [map_mul, map_mul, Complex.conj_conj, ← Circle.coe_inv_eq_conj, ← Circle.coe_inv_eq_conj,
      ← Circle.exp_neg, ← eC_neg]
    have key : Circle.exp (-(Real.pi / K.σ.p₃)) * eC (-(K.a₃ * (-K.sThree x + K.k₃))) =
        Circle.exp (Real.pi / K.σ.p₃) * eC (K.a₃ * K.sThree x) := by
      rw [eC, eC, ← Circle.exp_add, ← Circle.exp_add]
      have hb : ((K.σ.p₃ : ℝ) * K.b₃ - K.a₃ * K.q₃) = 1 := by exact_mod_cast K.bez₃
      have : -(Real.pi / K.σ.p₃) + 2 * Real.pi * -(K.a₃ * (-K.sThree x + K.k₃)) =
          (Real.pi / K.σ.p₃ + 2 * Real.pi * (K.a₃ * K.sThree x)) +
            ((-K.b₃ : ℤ) : ℝ) * (2 * Real.pi) := by
        rw [k₃]
        have hp0 : (K.σ.p₃ : ℝ) ≠ 0 := by exact_mod_cast K.p₃_pos.ne'
        push_cast
        field_simp
        linear_combination 2 * hb
      rw [this, Circle.exp_add _ (((-K.b₃ : ℤ) : ℝ) * (2 * Real.pi)), Circle.exp_int_mul_two_pi,
        mul_one]
    have := congrArg (fun w : Circle => (w : ℂ) * planeOf x) key
    simp only [Circle.coe_mul] at this
    linear_combination this
  · change (eC (K.σ.p₃ * (-K.sThree x + K.k₃)))⁻¹ = eC (K.σ.p₃ * K.sThree x)
    rw [← eC_neg]
    have : -(K.σ.p₃ * (-K.sThree x + K.k₃)) = K.σ.p₃ * K.sThree x + ((-K.q₃ : ℤ) : ℝ) := by
      push_cast
      linear_combination -hk
    rw [this, eC_add, eC_int, mul_one]

def rotThreeInv (x : ModelCoordinates) : ModelCoordinates :=
  ofPlane (K.σ.refl 1 (conj (planeOf x))) (x 2 + K.ℓ * K.k₃)

theorem conjPair_tubeOne_reflect {x : ModelCoordinates} (hd : conj (planeOf x) ∈ discOne K.D) :
    conjPair (K.tubeOne (reflectMap K.c₀ x)) = K.tubeOne (K.rotThreeInv x) := by
  set w := conj (planeOf x) with hw
  have hβ := K.betaOne_refl_one hd
  have hℓ := K.ℓ_ne
  have hsum : K.sOne (reflectMap K.c₀ x) = -K.sOne (K.rotThreeInv x) := by
    simp only [sOne, planeOf_reflectMap, reflectMap_two, rotThreeInv, planeOf_ofPlane,
      ofPlane_apply_two, ← hw, hβ, c₀, phase_e]
    field_simp
    ring
  unfold tubeOne conjPair
  rw [hsum, planeOf_reflectMap, ← hw]
  apply Prod.ext
  · change conj (K.σ.rotOne w * (eC (K.a₁ * -K.sOne (K.rotThreeInv x)) : ℂ)) =
      K.σ.rotOne (planeOf (K.rotThreeInv x)) * (eC (K.a₁ * K.sOne (K.rotThreeInv x)) : ℂ)
    rw [map_mul, ← Circle.coe_inv_eq_conj, ← eC_neg, rotThreeInv, planeOf_ofPlane, ← hw,
      K.σ.rotOne_refl_one]
    congr 3
    ring
  · change (eC (K.σ.p₁ * -K.sOne (K.rotThreeInv x)))⁻¹ = eC (K.σ.p₁ * K.sOne (K.rotThreeInv x))
    rw [← eC_neg]
    congr 1
    ring

section Smooth

omit K in
theorem mainSet_ne_vertex {σ : EuclidShape} {D : σ.toCompactShape.FoldData} {z : ℂ}
    (hm : z ∈ mainSet D) : z ≠ σ.vertexOne ∧ z ≠ σ.vertexTwo := by
  have hk := kap_pos D
  rcases hm with ((h | h) | h) | h
  · exact ⟨ne_vertexOne_of_mem_intT h, ne_vertexTwo_of_mem_intT h⟩
  · obtain ⟨-, -, h2, -⟩ := h
    constructor <;> rintro rfl
    · rw [σ.wallSide_two_vertexOne] at h2; linarith
    · rw [σ.wallSide_two_vertexTwo] at h2; linarith
  · obtain ⟨-, h0, h2, -⟩ := h
    constructor <;> rintro rfl
    · rw [σ.wallSide_two_vertexOne] at h2; linarith
    · rw [σ.wallSide_zero_vertexTwo] at h0; linarith
  · obtain ⟨-, h0, h1, -⟩ := h
    constructor <;> rintro rfl
    · rw [σ.wallSide_one_vertexOne] at h1; linarith
    · rw [σ.wallSide_zero_vertexTwo] at h0; linarith

omit K in
theorem mainSet_phase {σ : EuclidShape} {D : σ.toCompactShape.FoldData} {z : ℂ}
    (hm : z ∈ mainSet D) : D.f z ∈ phaseDomain (3 / 2) ∧ D.f z ∈ phaseDomain (-(3 / 2)) ∧
      (D.f z ∈ phaseDomain 0 ∨ normSq (D.f z) < 121 / 16) := by
  rcases hm with ((h | h) | h) | h
  · have := im_f_pos_of_intT D h
    exact ⟨mem_phaseDomain_iff.2 (Or.inl this), mem_phaseDomain_iff.2 (Or.inl this),
      Or.inl (mem_phaseDomain_iff.2 (Or.inl this))⟩
  · have hre := h.2.2.2.2.2.1
    exact ⟨mem_phaseDomain_of_re_ne (by linarith), mem_phaseDomain_of_re_ne (by linarith),
      Or.inl (mem_phaseDomain_of_re_ne (by linarith))⟩
  · have hre := h.2.2.2.2.2.1
    exact ⟨mem_phaseDomain_of_re_ne (by linarith), mem_phaseDomain_of_re_ne (by linarith),
      Or.inl (mem_phaseDomain_of_re_ne (by linarith))⟩
  · have h1 := h.2.2.2.2.2.1
    have h2 := h.2.2.2.2.2.2.1
    have h3 := h.2.2.2.2.2.2.2.1
    exact ⟨mem_phaseDomain_of_re_ne (by linarith), mem_phaseDomain_of_re_ne (by linarith),
      Or.inr (by linarith)⟩

theorem contMDiffOn_psiC : ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 1) ∞ K.psiC (mainSet K.D) := by
  intro z hz
  have hU := mainSet_subset_U K.D hz
  have hf : ContDiffAt ℝ ∞ K.D.f z := K.D.contDiffOn_f.contDiffAt (K.D.isOpen_U.mem_nhds hU)
  obtain ⟨h1, h2, h3⟩ := mainSet_phase hz
  have hθ := K.phase.contDiffAt_theta (z₀ := z) h1 h2 h3
  have hc : ContDiffAt ℝ ∞ (fun w => -(K.phase.theta w (K.D.f w))) z :=
    (hθ.comp z (contDiffAt_id.prodMk hf)).neg
  exact (contMDiff_circleExp.contMDiffAt.comp z hc.contMDiffAt).contMDiffWithinAt

theorem isLocalDiffeomorphAt_liftP {x : ModelCoordinates} (hm : planeOf x ∈ mainSet K.D) :
    IsLocalDiffeomorphAt (𝓡 3) PlaneCircleModel ∞ K.liftP x := by
  obtain ⟨hne1, hne2⟩ := mainSet_ne_vertex hm
  have hU := mainSet_subset_U K.D hm
  exact isLocalDiffeomorphAt_flatBaseLift (isOpen_mainSet K.D)
    (K.D.contDiffOn_f.mono (mainSet_subset_U K.D)) K.contMDiffOn_psiC K.ℓ_ne hm
    (det_fderiv_pos' K.D hU hne1 hne2).ne'

theorem isLocalDiffeomorphAt_liftM {x : ModelCoordinates}
    (hm : conj (planeOf x) ∈ mainSet K.D) :
    IsLocalDiffeomorphAt (𝓡 3) PlaneCircleModel ∞ K.liftM x := by
  have hm' : planeOf (reflectDiffeo K.c₀ x) ∈ mainSet K.D := by
    rw [reflectDiffeo_apply, planeOf_reflectMap]; exact hm
  have h1 := IsLocalDiffeomorphAt.comp (hf := (reflectDiffeo K.c₀).isLocalDiffeomorph x)
    (hg := K.isLocalDiffeomorphAt_liftP hm')
  exact IsLocalDiffeomorphAt.comp (hf := h1) (hg := conjPairDiffeo.isLocalDiffeomorph _)

omit K in
theorem contDiff_rotOne (σ : EuclidShape) : ContDiff ℝ ∞ σ.rotOne := by
  unfold EuclidShape.rotOne
  exact (contDiff_const.mul (contDiff_id.sub contDiff_const)).neg

omit K in
theorem contDiff_rotTwo (σ : EuclidShape) : ContDiff ℝ ∞ σ.rotTwo := by
  unfold EuclidShape.rotTwo
  exact (contDiff_const.mul (contDiff_id.sub contDiff_const)).neg

omit K in
theorem contDiff_apexOne (σ : EuclidShape) : ContDiff ℝ ∞ σ.apexOne := by
  unfold EuclidShape.apexOne
  exact contDiff_const.add (((contDiff_rotOne σ).pow _).div_const _)

omit K in
theorem contDiff_apexTwo (σ : EuclidShape) : ContDiff ℝ ∞ σ.apexTwo := by
  unfold EuclidShape.apexTwo
  exact contDiff_const.add (((contDiff_rotTwo σ).pow _).div_const _)

theorem contDiffOn_betaOne : ContDiffOn ℝ ∞ K.betaOne (discOne K.D) := by
  intro z hz
  have hph := contDiffAt_phaseArg (c := -(3 / 2)) (mem_phaseDomain_of_re_ne
    (ne_of_gt (K.re_apexOne_gt hz)))
  have h := hph.comp z (contDiff_apexOne K.σ).contDiffAt
  exact ((((K.phase.contDiff_psi _).contDiffAt.div_const _).neg).sub
    (((contDiffAt_const.mul h).sub contDiffAt_const).div_const _)).contDiffWithinAt

theorem contDiffOn_betaTwo : ContDiffOn ℝ ∞ K.betaTwo (discTwo K.D) := by
  intro z hz
  have hph := contDiffAt_phaseArg (c := 3 / 2) (mem_phaseDomain_of_re_ne
    (ne_of_lt (K.re_apexTwo_lt hz)))
  have h := hph.comp z (contDiff_apexTwo K.σ).contDiffAt
  exact ((((K.phase.contDiff_psi _).contDiffAt.div_const _).neg).sub
    ((contDiffAt_const.mul h).div_const _)).contDiffWithinAt

theorem isLocalDiffeomorphAt_tubeOne {x : ModelCoordinates} (hd : planeOf x ∈ discOne K.D) :
    IsLocalDiffeomorphAt (𝓡 3) PlaneCircleModel ∞ K.tubeOne x := by
  have hμ : -exp (-((K.σ.θ₃ : ℂ) * I)) ≠ 0 := neg_ne_zero.2 (Complex.exp_ne_zero _)
  have h := isLocalDiffeomorphAt_flatTubeLift hμ K.σ.vertexOne K.a₁ K.p₁_pos.ne' K.ℓ_ne
    (isOpen_discOne K.D) K.contDiffOn_betaOne hd
  refine IsLocalDiffeomorphAt.of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_) h
  simp only [tubeOne, sOne, EuclidShape.rotOne]
  congr 1
  ring

theorem isLocalDiffeomorphAt_tubeTwo {x : ModelCoordinates} (hd : planeOf x ∈ discTwo K.D) :
    IsLocalDiffeomorphAt (𝓡 3) PlaneCircleModel ∞ K.tubeTwo x := by
  have hμ : -exp ((K.σ.θ₂ : ℂ) * I) ≠ 0 := neg_ne_zero.2 (Complex.exp_ne_zero _)
  have h := isLocalDiffeomorphAt_flatTubeLift hμ K.σ.vertexTwo K.a₂ K.p₂_pos.ne' K.ℓ_ne
    (isOpen_discTwo K.D) K.contDiffOn_betaTwo hd
  refine IsLocalDiffeomorphAt.of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_) h
  simp only [tubeTwo, sTwo, EuclidShape.rotTwo]
  congr 1
  ring

theorem isLocalDiffeomorphAt_tubeThree (x : ModelCoordinates) :
    IsLocalDiffeomorphAt (𝓡 3) PlaneCircleModel ∞ K.tubeThree x := by
  have hμ : (Circle.exp (Real.pi / K.σ.p₃) : ℂ) ≠ 0 := Circle.coe_ne_zero _
  have h := isLocalDiffeomorphAt_flatTubeLift hμ 0 K.a₃ K.p₃_pos.ne' K.ℓ_ne
    (β := fun _ => K.betaThree) isOpen_univ contDiffOn_const (mem_univ (planeOf x))
  refine IsLocalDiffeomorphAt.of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_) h
  simp only [tubeThree, sThree, sub_zero]

end Smooth

section Screws

theorem base_le : K.m.baseCurvature ≤ 0 := le_of_eq K.base_flat

def pOne : ℕ+ := ⟨K.σ.p₁, K.p₁_pos⟩

def pTwo : ℕ+ := ⟨K.σ.p₂, K.p₂_pos⟩

def pThree : ℕ+ := ⟨K.σ.p₃, K.p₃_pos⟩

def screwOne : ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates :=
  screwAt K.m K.base_le (ofPlane K.σ.vertexOne 0) K.pOne K.q₁ K.ℓ

def screwTwo : ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates :=
  screwAt K.m K.base_le (ofPlane K.σ.vertexTwo 0) K.pTwo K.q₂ K.ℓ

def screwThree : ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates :=
  screwAt K.m K.base_le (ofPlane 0 0) K.pThree K.q₃ K.ℓ

theorem metric_screwOne :
    Diffeomorph.pullbackMetric K.m.coneProfile.metric K.screwOne = K.m.coneProfile.metric :=
  screwAt_isometry _ _ _ _ _ _

theorem metric_screwTwo :
    Diffeomorph.pullbackMetric K.m.coneProfile.metric K.screwTwo = K.m.coneProfile.metric :=
  screwAt_isometry _ _ _ _ _ _

theorem metric_screwThree :
    Diffeomorph.pullbackMetric K.m.coneProfile.metric K.screwThree = K.m.coneProfile.metric :=
  screwAt_isometry _ _ _ _ _ _

theorem planeOf_screw (v : ℂ) (p : ℕ+) (q : ℤ) (x : ModelCoordinates) :
    planeOf (screwAt K.m K.base_le (ofPlane v 0) p q K.ℓ x) =
      v + (Circle.exp (-2 * Real.pi / p) : ℂ) * (planeOf x - v) := by
  rw [planeOf_screwAt_flat _ _ K.base_flat, planeOf_ofPlane]

theorem two_screw (v : ℂ) (p : ℕ+) (q : ℤ) (x : ModelCoordinates) :
    screwAt K.m K.base_le (ofPlane v 0) p q K.ℓ x 2 =
      x 2 - K.ℓ * q / p - K.c * planeCrossC v ((Circle.exp (-2 * Real.pi / p) : ℂ) *
        (planeOf x - v) - (planeOf x - v)) / 2 := by
  rw [screwAt_flat_two _ _ K.base_flat, planeOf_ofPlane]
  rfl

theorem coe_pThree : ((K.pThree : ℕ) : ℝ) = K.σ.p₃ := rfl

theorem screwThree_rotThreeInv (x : ModelCoordinates) : K.screwThree (K.rotThreeInv x) = x := by
  apply modelCoordinates_ext
  · rw [screwThree, planeOf_screw, rotThreeInv, planeOf_ofPlane, sub_zero, zero_add]
    change (Circle.exp (-2 * Real.pi / K.σ.p₃) : ℂ) *
      (exp (2 * (K.σ.θ₃ : ℂ) * I) * conj (conj (planeOf x))) = planeOf x
    rw [Complex.conj_conj, Circle.coe_exp, ← mul_assoc, ← Complex.exp_add]
    have hθ := p_inv_eq K.p₃_pos K.σ.θ₃_mul
    have : ((-2 * Real.pi / K.σ.p₃ : ℝ) : ℂ) * I + 2 * (K.σ.θ₃ : ℂ) * I = 0 := by
      rw [hθ]
      push_cast
      ring
    rw [this, Complex.exp_zero, one_mul]
  · rw [screwThree, two_screw, rotThreeInv, ofPlane_apply_two]
    simp only [planeCrossC, zero_re, zero_im, zero_mul, sub_zero, mul_zero, zero_div]
    rw [coe_pThree, k₃]
    have hp : (K.σ.p₃ : ℝ) ≠ 0 := by exact_mod_cast K.p₃_pos.ne'
    field_simp
    ring

theorem screwThree_symm (x : ModelCoordinates) : K.screwThree.symm x = K.rotThreeInv x := by
  conv_lhs => rw [← K.screwThree_rotThreeInv x]
  exact K.screwThree.symm_apply_apply _

end Screws

end FlatDatum

end ClosedTriangle

end GC.Seifert
