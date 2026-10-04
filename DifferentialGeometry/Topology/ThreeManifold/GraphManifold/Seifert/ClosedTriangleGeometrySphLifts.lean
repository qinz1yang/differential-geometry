import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometrySphTube
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryFlatLifts

/-!
# The model lifts of a spherical closed triangle fold and their apex identities

Lane B3d (design `docs/geometrization/handoffs/20261004-design-b3d-spherical-row.md`, §4–§5, with
review 32 §6). A `SphDatum` collects a spherical shape `σ`, a fold datum `D` on it, the twists and
Bézout columns `(qⱼ, aⱼ, bⱼ)` of the three cones (cone `3` at the outer hole), a nonzero signed
fibre step `ℓ` with `2π = n ℓ` (`n ∈ ℤ`) and the closing equation `ℓ e = θ₁ + θ₂ + θ₃ - π`.
On `ModelCoordinates` (`z = planeOf x` the stereographic coordinate of the Hopf base, `t = x 2`):
* the base lift `liftP x = (f z, e(t/ℓ) e^{-iΘ(z, f z)})` with the spherical phase `Θ`
  (`SphPhaseData.theta`) and its mirror `liftM = conjPair ∘ liftP ∘ reflectMap c₀`,
  `c₀ = ℓ (k₁ + k₂)`;
* the tube coordinates `tubeOne x = (rotOne z e(a₁ s₁), e(p₁ s₁))`, `tubeTwo`, and
  `tubeThree x = (e^{iπ/p₃} z e(a₃ s₃), e(p₃ s₃))`, with ONE convention `sⱼ = t/ℓ + βⱼ z`,
  `β₁ = -ψ₁/ℓ - (k₂ φ_{-3/2}(apexOne) - π e)/2π`, `β₂ = -ψ₂/ℓ - k₁ φ_{3/2}(apexTwo)/2π`,
  `β₃ = k₃ + e/2` (`ψ_v = psiS v`; the gauge enters once).
In the good sector of each vertex the base lift is the seam model of the tube coordinates
(`liftP_eq_seamFwd_tubeOne`, `liftP_eq_seamFwd_tubeTwo`, `liftP_eq_outerFwd_tubeThree`), and the
inner tube coordinates are the spherical tube maps of `SphTube` (`tubeOne_eq_sphTube`,
`tubeTwo_eq_sphTube`).
-/

set_option autoImplicit false

noncomputable section
open Set Complex
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Topology ComplexConjugate ContDiff Manifold

namespace GC.Seifert

namespace ClosedTriangle

namespace Sph

open TwoConeFold

def apexOneS (σ : CompactShape) (z : ℂ) : ℂ := 3 / 2 + σ.rotOne z ^ σ.p₁ / 2

def apexTwoS (σ : CompactShape) (z : ℂ) : ℂ := -(3 / 2) + σ.rotTwo z ^ σ.p₂ / 2

theorem disc_of_sph {σ : CompactShape} (hσ : σ.curv = .spherical) (v z : ℂ) :
    σ.disc v z = discV v z := by
  have he : σ.eps = -1 := by
    unfold CompactShape.eps
    rw [hσ]
    rfl
  simp [CompactShape.disc, discV, he]

theorem rotOne_eq_of_sph {σ : CompactShape} (hσ : σ.curv = .spherical) (z : ℂ) :
    σ.rotOne z = -exp (-((σ.θ₃ : ℂ) * I)) * discV σ.vertexOne z := by
  rw [CompactShape.rotOne, disc_of_sph hσ]
  ring

theorem rotTwo_eq_of_sph {σ : CompactShape} (hσ : σ.curv = .spherical) (z : ℂ) :
    σ.rotTwo z = -exp ((σ.θ₂ : ℂ) * I) * discV σ.vertexTwo z := by
  rw [CompactShape.rotTwo, disc_of_sph hσ]
  ring

theorem conj_vertexTwo_sph (σ : CompactShape) : conj σ.vertexTwo = σ.vertexTwo := by
  rw [CompactShape.vertexTwo, conj_ofReal]

theorem discV_conj_of_real {v : ℂ} (hv : conj v = v) (z : ℂ) :
    discV v (conj z) = conj (discV v z) := by
  unfold discV
  rw [map_div₀, map_sub, map_add, map_one, map_mul, conj_conj, hv]

theorem rotTwo_conj_sph {σ : CompactShape} (hσ : σ.curv = .spherical) (z : ℂ) :
    σ.rotTwo (conj z) = exp (2 * (σ.θ₂ : ℂ) * I) * conj (σ.rotTwo z) := by
  have hc : conj (exp ((σ.θ₂ : ℂ) * I)) = exp (-((σ.θ₂ : ℂ) * I)) := by
    rw [← exp_conj, map_mul, conj_ofReal, conj_I, mul_neg]
  have e : exp (2 * (σ.θ₂ : ℂ) * I) * exp (-((σ.θ₂ : ℂ) * I)) = exp ((σ.θ₂ : ℂ) * I) := by
    rw [← exp_add]
    ring_nf
  rw [rotTwo_eq_of_sph hσ, rotTwo_eq_of_sph hσ, discV_conj_of_real (conj_vertexTwo_sph σ),
    map_mul, map_neg, hc]
  linear_combination (conj (discV σ.vertexTwo z)) * e

theorem rotOne_refl_one_sph {σ : CompactShape} (hσ : σ.curv = .spherical) (z : ℂ) :
    σ.rotOne (σ.refl 1 z) = conj (σ.rotOne z) := by
  rw [rotOne_eq_of_sph hσ, rotOne_eq_of_sph hσ]
  change -exp (-((σ.θ₃ : ℂ) * I)) * discV σ.vertexOne (exp (2 * (σ.θ₃ : ℂ) * I) * conj z) = _
  set E := exp ((σ.θ₃ : ℂ) * I) with hE
  have hE0 : E ≠ 0 := exp_ne_zero _
  have hcE : conj E = E⁻¹ := by
    rw [hE, ← exp_conj, map_mul, conj_ofReal, conj_I, ← exp_neg]
    ring_nf
  have h2 : exp (2 * (σ.θ₃ : ℂ) * I) = E * E := by rw [hE, ← exp_add]; ring_nf
  have hm : exp (-((σ.θ₃ : ℂ) * I)) = E⁻¹ := by rw [hE, exp_neg]
  have hv : σ.vertexOne = (σ.sideTan σ.θ₁ σ.θ₃ σ.θ₂ : ℂ) * E := rfl
  rw [h2, hm, hv]
  unfold discV
  simp only [map_neg, map_mul, map_div₀, map_sub, map_add, map_one, conj_ofReal, hcE, map_inv₀,
    inv_inv]
  set t := (σ.sideTan σ.θ₁ σ.θ₃ σ.θ₂ : ℂ)
  have d1 : 1 + t * E⁻¹ * (E * E * conj z) = 1 + t * E * conj z := by
    field_simp
  have n1 : E * E * conj z - t * E = E * (E * conj z - t) := by ring
  have n2 : E * (conj z - t * E⁻¹) = E * conj z - t := by
    field_simp
  rw [d1, n1, mul_div_assoc', ← mul_assoc, neg_mul, inv_mul_cancel₀ hE0, neg_mul, one_mul,
    mul_div_assoc', neg_mul, n2]

theorem apexOneS_refl_one {σ : CompactShape} (hσ : σ.curv = .spherical) (z : ℂ) :
    apexOneS σ (σ.refl 1 z) = conj (apexOneS σ z) := by
  unfold apexOneS
  rw [rotOne_refl_one_sph hσ]
  simp only [map_add, map_div₀, map_pow, map_ofNat]

theorem apexTwoS_conj {σ : CompactShape} (hσ : σ.curv = .spherical) (z : ℂ) :
    apexTwoS σ (conj z) = conj (apexTwoS σ z) := by
  unfold apexTwoS
  have hp : (σ.p₂ : ℂ) ≠ 0 := by
    have : 0 < σ.p₂ := by have := σ.two_le_p₂; omega
    exact_mod_cast this.ne'
  have h2 : exp (2 * (σ.θ₂ : ℂ) * I) ^ σ.p₂ = 1 := by
    rw [← exp_nat_mul]
    have : (σ.p₂ : ℂ) * (2 * (σ.θ₂ : ℂ) * I) = (1 : ℤ) * (2 * Real.pi * I) := by
      rw [CompactShape.θ₂]
      push_cast
      field_simp
    rw [this]
    exact exp_int_mul_two_pi_mul_I 1
  rw [rotTwo_conj_sph hσ, mul_pow, h2, one_mul]
  simp only [map_add, map_neg, map_div₀, map_pow, map_ofNat]

structure SphDatum where
  σ : CompactShape
  hσ : σ.curv = .spherical
  D : σ.FoldData
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
  ℓ : ℝ
  ℓ_ne : ℓ ≠ 0
  n : ℤ
  period : 2 * Real.pi = n * ℓ
  closing : ℓ * -((q₁ : ℝ) / σ.p₁ + (q₂ : ℝ) / σ.p₂ + (q₃ : ℝ) / σ.p₃) =
    σ.θ₁ + σ.θ₂ + σ.θ₃ - Real.pi

namespace SphDatum

variable (K : SphDatum)

def k₁ : ℝ := (K.q₁ : ℝ) / K.σ.p₁

def k₂ : ℝ := (K.q₂ : ℝ) / K.σ.p₂

def k₃ : ℝ := (K.q₃ : ℝ) / K.σ.p₃

def phase : SphPhaseData := ⟨K.k₁, K.k₂, K.k₃, K.ℓ, K.σ.vertexOne, K.σ.vertexTwo⟩

def c₀ : ℝ := K.ℓ * (K.k₁ + K.k₂)

def psiC (z : ℂ) : Circle := Circle.exp (-(K.phase.theta z (K.D.f z)))

def liftP (x : ModelCoordinates) : ℂ × Circle :=
  (K.D.f (planeOf x), eC (x 2 / K.ℓ) * K.psiC (planeOf x))

def liftM (x : ModelCoordinates) : ℂ × Circle := conjPair (K.liftP (reflectMap K.c₀ x))

def betaHatOne (z : ℂ) : ℝ :=
  -(K.k₂ * phaseArg (-(3 / 2)) (apexOneS K.σ z) - Real.pi * K.phase.e) / (2 * Real.pi)

def betaHatTwo (z : ℂ) : ℝ := -(K.k₁ * phaseArg (3 / 2) (apexTwoS K.σ z)) / (2 * Real.pi)

def betaOne (z : ℂ) : ℝ := -psiS K.σ.vertexOne z / K.ℓ + K.betaHatOne z

def betaTwo (z : ℂ) : ℝ := -psiS K.σ.vertexTwo z / K.ℓ + K.betaHatTwo z

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

@[simp] theorem phase_k₁ : K.phase.k₁ = K.k₁ := rfl

@[simp] theorem phase_k₂ : K.phase.k₂ = K.k₂ := rfl

@[simp] theorem phase_k₃ : K.phase.k₃ = K.k₃ := rfl

@[simp] theorem phase_ℓ : K.phase.ℓ = K.ℓ := rfl

@[simp] theorem phase_v₁ : K.phase.v₁ = K.σ.vertexOne := rfl

@[simp] theorem phase_v₂ : K.phase.v₂ = K.σ.vertexTwo := rfl

theorem phase_e : K.phase.e = -(K.k₁ + K.k₂ + K.k₃) := rfl

theorem θ₁_mul : K.σ.θ₁ * K.σ.p₁ = Real.pi := by
  rw [CompactShape.θ₁, div_mul_cancel₀ _ (by exact_mod_cast K.p₁_pos.ne')]

theorem θ₂_mul : K.σ.θ₂ * K.σ.p₂ = Real.pi := by
  rw [CompactShape.θ₂, div_mul_cancel₀ _ (by exact_mod_cast K.p₂_pos.ne')]

theorem θ₃_mul : K.σ.θ₃ * K.σ.p₃ = Real.pi := by
  rw [CompactShape.θ₃, div_mul_cancel₀ _ (by exact_mod_cast K.p₃_pos.ne')]

theorem closing_phase : K.ℓ * K.phase.e = K.σ.θ₁ + K.σ.θ₂ + K.σ.θ₃ - Real.pi := by
  rw [phase_e, ← K.closing]
  rfl

theorem liftP_eq_seamFwd_tubeOne {x : ModelCoordinates}
    (hf : K.D.f (planeOf x) = apexOneS K.σ (planeOf x))
    (hn : ‖K.σ.rotOne (planeOf x)‖ ^ K.σ.p₁ ≤ 1)
    (hs : K.σ.rotOne (planeOf x) ≠ 0 ∧ -(K.σ.θ₁ / 2) < arg (K.σ.rotOne (planeOf x)) ∧
      arg (K.σ.rotOne (planeOf x)) < 3 * K.σ.θ₁ / 2) :
    K.liftP x = seamFwd ((3 / 2 : ℝ) : ℂ) K.σ.p₁ K.σ.p₁ K.q₁ K.a₁ K.b₁ (K.tubeOne x) := by
  obtain ⟨hne, h1, h2⟩ := hs
  obtain ⟨b1, b2⟩ := FlatDatum.mul_arg_bounds K.θ₁_mul h1 h2
  set z := planeOf x with hz
  set η := K.σ.rotOne z with hη
  have hap := seamFwd_apex (c := ((3 / 2 : ℝ) : ℂ)) (P := K.σ.p₁) (p := K.σ.p₁) (q := K.q₁)
    (a := K.a₁) (b := K.b₁) K.bez₁ rfl η hne (K.sOne x)
  have hfz : K.D.f z = 3 / 2 + η ^ K.σ.p₁ / 2 := hf
  have hθ := K.phase.theta_vertexOne (z := z) hfz hne hn b1 b2.le
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
  have hapex : apexOneS K.σ z = 3 / 2 + η ^ K.σ.p₁ / 2 := rfl
  rw [psiC, hθ, hfz, FlatDatum.circle_exp_arg_zpow hne, eC, ← Circle.exp_add, ← Circle.exp_add]
  congr 1
  have hk := K.k₁_mul
  have hℓ := K.ℓ_ne
  simp only [sOne, betaOne, betaHatOne, ← hz, hapex, phase_k₁, phase_k₂, phase_ℓ, phase_v₁]
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  push_cast
  field_simp
  linear_combination (-(K.ℓ * arg η)) * hk

theorem liftP_eq_seamFwd_tubeTwo {x : ModelCoordinates}
    (hf : K.D.f (planeOf x) = apexTwoS K.σ (planeOf x))
    (hn : ‖K.σ.rotTwo (planeOf x)‖ ^ K.σ.p₂ ≤ 1)
    (hs : K.σ.rotTwo (planeOf x) ≠ 0 ∧ -(K.σ.θ₂ / 2) < arg (K.σ.rotTwo (planeOf x)) ∧
      arg (K.σ.rotTwo (planeOf x)) < 3 * K.σ.θ₂ / 2) :
    K.liftP x = seamFwd ((-(3 / 2) : ℝ) : ℂ) K.σ.p₂ K.σ.p₂ K.q₂ K.a₂ K.b₂ (K.tubeTwo x) := by
  obtain ⟨hne, h1, h2⟩ := hs
  obtain ⟨b1, b2⟩ := FlatDatum.mul_arg_bounds K.θ₂_mul h1 h2
  set z := planeOf x with hz
  set η := K.σ.rotTwo z with hη
  have hap := seamFwd_apex (c := ((-(3 / 2) : ℝ) : ℂ)) (P := K.σ.p₂) (p := K.σ.p₂) (q := K.q₂)
    (a := K.a₂) (b := K.b₂) K.bez₂ rfl η hne (K.sTwo x)
  have hfz : K.D.f z = -(3 / 2) + η ^ K.σ.p₂ / 2 := hf
  have hθ := K.phase.theta_vertexTwo (z := z) hfz hne hn b1 b2.le
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
  have hapex : apexTwoS K.σ z = -(3 / 2) + η ^ K.σ.p₂ / 2 := rfl
  rw [psiC, hθ, hfz, FlatDatum.circle_exp_arg_zpow hne, eC, ← Circle.exp_add, ← Circle.exp_add]
  congr 1
  have hk := K.k₂_mul
  have hℓ := K.ℓ_ne
  simp only [sTwo, betaTwo, betaHatTwo, ← hz, hapex, phase_k₁, phase_k₂, phase_ℓ, phase_v₂]
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  push_cast
  field_simp
  linear_combination (-(K.ℓ * arg η)) * hk

theorem liftP_eq_outerFwd_tubeThree {x : ModelCoordinates}
    (hf : K.D.f (planeOf x) = compactOuterGerm K.σ.p₃ (planeOf x))
    (hn9 : 9 ≤ normSq (K.D.f (planeOf x))) (hzp : ‖planeOf x‖ ^ K.σ.p₃ < 7)
    (hs : planeOf x ≠ 0 ∧ -(K.σ.θ₃ / 2) < arg (planeOf x) ∧ arg (planeOf x) < 3 * K.σ.θ₃ / 2) :
    K.liftP x = outerFwd K.σ.p₃ K.σ.p₃ K.q₃ K.a₃ K.b₃ (K.tubeThree x) := by
  obtain ⟨hne, h1, h2⟩ := hs
  obtain ⟨b1, b2⟩ := FlatDatum.mul_arg_bounds K.θ₃_mul h1 h2
  set z := planeOf x with hz
  have hap := outerFwd_apex (P := K.σ.p₃) (p := K.σ.p₃) (q := K.q₃) (a := K.a₃) (b := K.b₃)
    K.bez₃ K.p₃_pos.ne' rfl z hne (K.sThree x)
  have hθ := K.phase.theta_outer (z := z) hn9
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
  rw [psiC, hθ, hf, hφ, FlatDatum.circle_exp_arg_zpow hne, eC, ← Circle.exp_add,
    ← Circle.exp_add, ← Circle.exp_add]
  congr 1
  have hk := K.k₃_mul
  have hℓ := K.ℓ_ne
  have hp3 : (K.σ.p₃ : ℝ) ≠ 0 := by exact_mod_cast K.p₃_pos.ne'
  simp only [sThree, betaThree, phase_k₃, phase_e]
  push_cast
  field_simp
  linear_combination (-(Real.pi * K.ℓ) - K.σ.p₃ * K.ℓ * arg z) * hk

theorem tubeOne_eq_sphTube (x : ModelCoordinates) :
    K.tubeOne x = sphTube K.σ.vertexOne (-exp (-((K.σ.θ₃ : ℂ) * I))) K.a₁ K.σ.p₁ K.ℓ
      (fun z => -psiS K.σ.vertexOne z / K.ℓ + K.betaHatOne z) x := by
  unfold tubeOne sphTube sphTubeS
  rw [rotOne_eq_of_sph K.hσ]
  rfl

theorem tubeTwo_eq_sphTube (x : ModelCoordinates) :
    K.tubeTwo x = sphTube K.σ.vertexTwo (-exp ((K.σ.θ₂ : ℂ) * I)) K.a₂ K.σ.p₂ K.ℓ
      (fun z => -psiS K.σ.vertexTwo z / K.ℓ + K.betaHatTwo z) x := by
  unfold tubeTwo sphTube sphTubeS
  rw [rotTwo_eq_of_sph K.hσ]
  rfl

theorem psi_vertexTwo_conj {z : ℂ} (hz : 1 + conj K.σ.vertexTwo * z ∈ slitPlane) :
    psiS K.σ.vertexTwo (conj z) = -psiS K.σ.vertexTwo z :=
  psiS_conj_of_real (conj_vertexTwo_sph K.σ) hz

theorem psi_vertexOne_refl_one {z : ℂ} (hz : 1 + conj K.σ.vertexOne * z ∈ slitPlane) :
    psiS K.σ.vertexOne (K.σ.refl 1 z) = -psiS K.σ.vertexOne z :=
  psiS_refl_one (r := K.σ.sideTan K.σ.θ₁ K.σ.θ₃ K.σ.θ₂) rfl hz

theorem liftM_eq_liftP {x : ModelCoordinates} (hV : planeOf x ∈ K.D.V 0)
    (hre : (K.D.f (planeOf x)).re < -(3 / 2))
    (hz : 1 + conj K.σ.vertexTwo * planeOf x ∈ slitPlane) : K.liftM x = K.liftP x := by
  set z := planeOf x with hzdef
  have hfl : K.D.f (conj z) = conj (K.D.f z) := K.D.f_refl 0 z hV
  have hθ := K.phase.theta_wallZero (z := z) (z' := conj z) hre (K.psi_vertexTwo_conj hz)
  unfold liftM liftP conjPair
  rw [planeOf_reflectMap, ← hzdef, hfl, Complex.conj_conj, reflectMap_two]
  congr 1
  rw [psiC, hfl, mul_inv, ← Circle.exp_neg, neg_neg, eC, eC, ← Circle.exp_neg, ← Circle.exp_add,
    psiC, ← Circle.exp_add]
  congr 1
  have hℓ := K.ℓ_ne
  simp only [c₀, phase_k₁, phase_k₂] at hθ ⊢
  field_simp
  linear_combination K.ℓ * hθ

theorem betaTwo_conj {z : ℂ} (hre : (apexTwoS K.σ z).re < 3 / 2)
    (hz : 1 + conj K.σ.vertexTwo * z ∈ slitPlane) :
    K.betaTwo (conj z) = -K.betaTwo z - K.k₁ := by
  have ha : apexTwoS K.σ (conj z) = conj (apexTwoS K.σ z) := apexTwoS_conj K.hσ z
  simp only [betaTwo, betaHatTwo, ha, phaseArg_conj_of_gt hre, K.psi_vertexTwo_conj hz]
  have hℓ := K.ℓ_ne
  field_simp
  ring

theorem betaOne_refl_one {z : ℂ} (hre : -(3 / 2) < (apexOneS K.σ z).re)
    (hz : 1 + conj K.σ.vertexOne * z ∈ slitPlane) :
    K.betaOne (K.σ.refl 1 z) = -K.betaOne z + K.phase.e := by
  have ha : apexOneS K.σ (K.σ.refl 1 z) = conj (apexOneS K.σ z) := apexOneS_refl_one K.hσ z
  simp only [betaOne, betaHatOne, ha, phaseArg_conj_of_lt hre, K.psi_vertexOne_refl_one hz]
  have hℓ := K.ℓ_ne
  field_simp
  ring

theorem conjPair_tubeTwo_reflect {x : ModelCoordinates}
    (hre : (apexTwoS K.σ (planeOf x)).re < 3 / 2)
    (hz : 1 + conj K.σ.vertexTwo * planeOf x ∈ slitPlane) :
    conjPair (K.tubeTwo (reflectMap K.c₀ x)) = K.tubeTwo x := by
  set z := planeOf x with hzdef
  have hβ := K.betaTwo_conj hre hz
  have hk := K.k₂_mul
  have hℓ := K.ℓ_ne
  have hθp := FlatDatum.p_inv_eq K.p₂_pos K.θ₂_mul
  have hsum : K.sTwo (reflectMap K.c₀ x) = -K.sTwo x + K.k₂ := by
    simp only [sTwo, planeOf_reflectMap, reflectMap_two, ← hzdef, hβ, c₀]
    field_simp
    ring
  unfold tubeTwo conjPair
  rw [hsum, planeOf_reflectMap, ← hzdef]
  apply Prod.ext
  · change conj (K.σ.rotTwo (conj z) * (eC (K.a₂ * (-K.sTwo x + K.k₂)) : ℂ)) =
      K.σ.rotTwo z * (eC (K.a₂ * K.sTwo x) : ℂ)
    have hr : K.σ.rotTwo (conj z) = exp (2 * (K.σ.θ₂ : ℂ) * I) * conj (K.σ.rotTwo z) :=
      rotTwo_conj_sph K.hσ z
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

theorem conjPair_tubeOne_reflect {x : ModelCoordinates}
    (hre : -(3 / 2) < (apexOneS K.σ (conj (planeOf x))).re)
    (hz : 1 + conj K.σ.vertexOne * conj (planeOf x) ∈ slitPlane) :
    conjPair (K.tubeOne (reflectMap K.c₀ x)) = K.tubeOne (K.rotThreeInv x) := by
  set w := conj (planeOf x) with hw
  have hβ := K.betaOne_refl_one hre hz
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
      rotOne_refl_one_sph K.hσ]
    congr 3
    ring
  · change (eC (K.σ.p₁ * -K.sOne (K.rotThreeInv x)))⁻¹ = eC (K.σ.p₁ * K.sOne (K.rotThreeInv x))
    rw [← eC_neg]
    congr 1
    ring

section Smooth

theorem contDiffOn_rotOne {O : Set ℂ} (hO : IsOpen O)
    (hOv : ∀ z ∈ O, 1 + conj K.σ.vertexOne * z ≠ 0) : ContDiffOn ℝ ∞ K.σ.rotOne O := by
  have h : ContDiffOn ℂ ∞ (fun z => -exp (-((K.σ.θ₃ : ℂ) * I)) * discV K.σ.vertexOne z) O :=
    ((differentiableOn_discV _ hOv).const_mul _).contDiffOn hO
  have e : K.σ.rotOne = fun z => -exp (-((K.σ.θ₃ : ℂ) * I)) * discV K.σ.vertexOne z :=
    funext (rotOne_eq_of_sph K.hσ)
  rw [e]
  exact h.restrict_scalars ℝ

theorem contDiffOn_rotTwo {O : Set ℂ} (hO : IsOpen O)
    (hOv : ∀ z ∈ O, 1 + conj K.σ.vertexTwo * z ≠ 0) : ContDiffOn ℝ ∞ K.σ.rotTwo O := by
  have h : ContDiffOn ℂ ∞ (fun z => -exp ((K.σ.θ₂ : ℂ) * I) * discV K.σ.vertexTwo z) O :=
    ((differentiableOn_discV _ hOv).const_mul _).contDiffOn hO
  have e : K.σ.rotTwo = fun z => -exp ((K.σ.θ₂ : ℂ) * I) * discV K.σ.vertexTwo z :=
    funext (rotTwo_eq_of_sph K.hσ)
  rw [e]
  exact h.restrict_scalars ℝ

theorem contDiffOn_betaOne {O : Set ℂ} (hO : IsOpen O)
    (hOv : ∀ z ∈ O, 1 + conj K.σ.vertexOne * z ∈ slitPlane)
    (hre : ∀ z ∈ O, -(3 / 2) < (apexOneS K.σ z).re) : ContDiffOn ℝ ∞ K.betaOne O := by
  intro z hz
  have hrot := (K.contDiffOn_rotOne hO fun w hw => slitPlane_ne_zero (hOv w hw)).contDiffAt
    (hO.mem_nhds hz)
  have hap : ContDiffAt ℝ ∞ (apexOneS K.σ) z :=
    contDiffAt_const.add ((hrot.pow _).div_const _)
  have hph := (contDiffAt_phaseArg (c := -(3 / 2)) (mem_phaseDomain_of_re_ne
    (ne_of_gt (hre z hz)))).comp z hap
  have hψ := contDiffAt_psiS K.σ.vertexOne (hOv z hz)
  exact (((hψ.neg).div_const _).add
    (((contDiffAt_const.mul hph).sub contDiffAt_const).neg.div_const _)).contDiffWithinAt

theorem contDiffOn_betaTwo {O : Set ℂ} (hO : IsOpen O)
    (hOv : ∀ z ∈ O, 1 + conj K.σ.vertexTwo * z ∈ slitPlane)
    (hre : ∀ z ∈ O, (apexTwoS K.σ z).re < 3 / 2) : ContDiffOn ℝ ∞ K.betaTwo O := by
  intro z hz
  have hrot := (K.contDiffOn_rotTwo hO fun w hw => slitPlane_ne_zero (hOv w hw)).contDiffAt
    (hO.mem_nhds hz)
  have hap : ContDiffAt ℝ ∞ (apexTwoS K.σ) z :=
    contDiffAt_const.add ((hrot.pow _).div_const _)
  have hph := (contDiffAt_phaseArg (c := 3 / 2) (mem_phaseDomain_of_re_ne
    (ne_of_lt (hre z hz)))).comp z hap
  have hψ := contDiffAt_psiS K.σ.vertexTwo (hOv z hz)
  exact (((hψ.neg).div_const _).add
    ((contDiffAt_const.mul hph).neg.div_const _)).contDiffWithinAt

theorem isLocalDiffeomorphAt_tubeOne {O : Set ℂ} (hO : IsOpen O)
    (hOv : ∀ z ∈ O, 1 + conj K.σ.vertexOne * z ∈ slitPlane)
    (hre : ∀ z ∈ O, -(3 / 2) < (apexOneS K.σ z).re) {x : ModelCoordinates}
    (hx : planeOf x ∈ O) : IsLocalDiffeomorphAt (𝓡 3) PlaneCircleModel ∞ K.tubeOne x := by
  have hμ : -exp (-((K.σ.θ₃ : ℂ) * I)) ≠ 0 := neg_ne_zero.2 (Complex.exp_ne_zero _)
  have hβ : ContDiffOn ℝ ∞ (fun z => -psiS K.σ.vertexOne z / K.ℓ + K.betaHatOne z) O :=
    K.contDiffOn_betaOne hO hOv hre
  have h := isLocalDiffeomorphAt_sphTube hμ K.a₁ K.p₁_pos.ne' K.ℓ_ne hO
    (fun z hz => slitPlane_ne_zero (hOv z hz)) hβ hx
  refine IsLocalDiffeomorphAt.of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_) h
  exact K.tubeOne_eq_sphTube y

theorem isLocalDiffeomorphAt_tubeTwo {O : Set ℂ} (hO : IsOpen O)
    (hOv : ∀ z ∈ O, 1 + conj K.σ.vertexTwo * z ∈ slitPlane)
    (hre : ∀ z ∈ O, (apexTwoS K.σ z).re < 3 / 2) {x : ModelCoordinates}
    (hx : planeOf x ∈ O) : IsLocalDiffeomorphAt (𝓡 3) PlaneCircleModel ∞ K.tubeTwo x := by
  have hμ : -exp ((K.σ.θ₂ : ℂ) * I) ≠ 0 := neg_ne_zero.2 (Complex.exp_ne_zero _)
  have hβ : ContDiffOn ℝ ∞ (fun z => -psiS K.σ.vertexTwo z / K.ℓ + K.betaHatTwo z) O :=
    K.contDiffOn_betaTwo hO hOv hre
  have h := isLocalDiffeomorphAt_sphTube hμ K.a₂ K.p₂_pos.ne' K.ℓ_ne hO
    (fun z hz => slitPlane_ne_zero (hOv z hz)) hβ hx
  refine IsLocalDiffeomorphAt.of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_) h
  exact K.tubeTwo_eq_sphTube y

theorem isLocalDiffeomorphAt_tubeThree (x : ModelCoordinates) :
    IsLocalDiffeomorphAt (𝓡 3) PlaneCircleModel ∞ K.tubeThree x := by
  have hμ : (Circle.exp (Real.pi / K.σ.p₃) : ℂ) ≠ 0 := Circle.coe_ne_zero _
  have h := isLocalDiffeomorphAt_flatTubeLift hμ 0 K.a₃ K.p₃_pos.ne' K.ℓ_ne
    (β := fun _ => K.betaThree) isOpen_univ contDiffOn_const (mem_univ (planeOf x))
  refine IsLocalDiffeomorphAt.of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_) h
  simp only [tubeThree, sThree, sub_zero]

theorem contMDiffOn_psiC {O : Set ℂ} (hOU : O ⊆ K.D.U)
    (hph : ∀ z ∈ O, K.D.f z ∈ phaseDomain (3 / 2) ∧ K.D.f z ∈ phaseDomain (-(3 / 2)) ∧
      (K.D.f z ∈ phaseDomain 0 ∨ normSq (K.D.f z) < 121 / 16))
    (h1 : ∀ z ∈ O, 1 + conj K.σ.vertexOne * z ∈ slitPlane)
    (h2 : ∀ z ∈ O, 1 + conj K.σ.vertexTwo * z ∈ slitPlane) :
    ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 1) ∞ K.psiC O := by
  intro z hz
  have hf : ContDiffAt ℝ ∞ K.D.f z :=
    K.D.contDiffOn_f.contDiffAt (K.D.isOpen_U.mem_nhds (hOU hz))
  obtain ⟨p1, p2, p3⟩ := hph z hz
  have hθ := K.phase.contDiffAt_theta (z₀ := z) p1 p2 p3 (h1 z hz) (h2 z hz)
  have hc : ContDiffAt ℝ ∞ (fun w => -(K.phase.theta w (K.D.f w))) z :=
    (hθ.comp z (contDiffAt_id.prodMk hf)).neg
  exact (contMDiff_circleExp.contMDiffAt.comp z hc.contMDiffAt).contMDiffWithinAt

theorem isLocalDiffeomorphAt_liftP {O : Set ℂ} (hO : IsOpen O) (hOU : O ⊆ K.D.U)
    (hph : ∀ z ∈ O, K.D.f z ∈ phaseDomain (3 / 2) ∧ K.D.f z ∈ phaseDomain (-(3 / 2)) ∧
      (K.D.f z ∈ phaseDomain 0 ∨ normSq (K.D.f z) < 121 / 16))
    (h1 : ∀ z ∈ O, 1 + conj K.σ.vertexOne * z ∈ slitPlane)
    (h2 : ∀ z ∈ O, 1 + conj K.σ.vertexTwo * z ∈ slitPlane)
    (hv : ∀ z ∈ O, z ≠ K.σ.vertexOne ∧ z ≠ K.σ.vertexTwo) {x : ModelCoordinates}
    (hx : planeOf x ∈ O) : IsLocalDiffeomorphAt (𝓡 3) PlaneCircleModel ∞ K.liftP x :=
  isLocalDiffeomorphAt_flatBaseLift hO (K.D.contDiffOn_f.mono hOU)
    (K.contMDiffOn_psiC hOU hph h1 h2) K.ℓ_ne hx
    (K.D.det_fderiv_pos _ (hOU hx) (hv _ hx).1 (hv _ hx).2).ne'

theorem isLocalDiffeomorphAt_liftM {O : Set ℂ} (hO : IsOpen O) (hOU : O ⊆ K.D.U)
    (hph : ∀ z ∈ O, K.D.f z ∈ phaseDomain (3 / 2) ∧ K.D.f z ∈ phaseDomain (-(3 / 2)) ∧
      (K.D.f z ∈ phaseDomain 0 ∨ normSq (K.D.f z) < 121 / 16))
    (h1 : ∀ z ∈ O, 1 + conj K.σ.vertexOne * z ∈ slitPlane)
    (h2 : ∀ z ∈ O, 1 + conj K.σ.vertexTwo * z ∈ slitPlane)
    (hv : ∀ z ∈ O, z ≠ K.σ.vertexOne ∧ z ≠ K.σ.vertexTwo) {x : ModelCoordinates}
    (hx : conj (planeOf x) ∈ O) : IsLocalDiffeomorphAt (𝓡 3) PlaneCircleModel ∞ K.liftM x := by
  have hm' : planeOf (reflectDiffeo K.c₀ x) ∈ O := by
    rw [reflectDiffeo_apply, planeOf_reflectMap]; exact hx
  have h1' := IsLocalDiffeomorphAt.comp (hf := (reflectDiffeo K.c₀).isLocalDiffeomorph x)
    (hg := K.isLocalDiffeomorphAt_liftP hO hOU hph h1 h2 hv hm')
  exact IsLocalDiffeomorphAt.comp (hf := h1') (hg := conjPairDiffeo.isLocalDiffeomorph _)

end Smooth

end SphDatum

end Sph

end ClosedTriangle

end GC.Seifert
