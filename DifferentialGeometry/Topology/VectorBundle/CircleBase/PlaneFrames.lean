import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Orthonormal pairs in a Euclidean plane: rotation, reflection, orientation sign

Linear algebra for the circle-base frame construction (P1a). For pairs `x y : Fin 2 → W` in a real
inner product space `W` of dimension two:

* `planeRot θ y` rotates the pair `y` by the angle `θ`, `planeFlip y = (y₀, -y₁)`;
* `planeDet x y = ⟪x₀, y₀⟫⟪x₁, y₁⟫ - ⟪x₀, y₁⟫⟪x₁, y₀⟫` is `±1` on orthonormal pairs
  (`planeDet_sq_eq_one`);
* an orthonormal pair `x` with `planeDet x y > 0` is the rotation of `y` by any angle with
  `cos θ = ⟪x₀, y₀⟫`, `sin θ = ⟪x₀, y₁⟫` (`eq_planeRot_of_planeDet_pos`).
-/

set_option autoImplicit false

noncomputable section

open scoped InnerProductSpace

namespace DifferentialGeometry.Topology.VectorBundle

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- Rotation of a pair of vectors by the angle `θ`. -/
def planeRot (θ : ℝ) (y : Fin 2 → W) : Fin 2 → W :=
  ![Real.cos θ • y 0 + Real.sin θ • y 1, -Real.sin θ • y 0 + Real.cos θ • y 1]

/-- Reflection of a pair: the second vector changes sign. -/
def planeFlip (y : Fin 2 → W) : Fin 2 → W := ![y 0, -y 1]

/-- The orientation determinant `⟪x₀, y₀⟫⟪x₁, y₁⟫ - ⟪x₀, y₁⟫⟪x₁, y₀⟫` of two pairs. -/
def planeDet (x y : Fin 2 → W) : ℝ :=
  ⟪x 0, y 0⟫_ℝ * ⟪x 1, y 1⟫_ℝ - ⟪x 0, y 1⟫_ℝ * ⟪x 1, y 0⟫_ℝ

@[simp] theorem planeRot_zero' (θ : ℝ) (y : Fin 2 → W) :
    planeRot θ y 0 = Real.cos θ • y 0 + Real.sin θ • y 1 := rfl

@[simp] theorem planeRot_one' (θ : ℝ) (y : Fin 2 → W) :
    planeRot θ y 1 = -Real.sin θ • y 0 + Real.cos θ • y 1 := rfl

omit [InnerProductSpace ℝ W] in
@[simp] theorem planeFlip_zero (y : Fin 2 → W) : planeFlip y 0 = y 0 := rfl

omit [InnerProductSpace ℝ W] in
@[simp] theorem planeFlip_one (y : Fin 2 → W) : planeFlip y 1 = -y 1 := rfl

theorem orthonormal_fin_two_iff {y : Fin 2 → W} :
    Orthonormal ℝ y ↔ ‖y 0‖ = 1 ∧ ‖y 1‖ = 1 ∧ ⟪y 0, y 1⟫_ℝ = 0 := by
  constructor
  · intro h
    exact ⟨h.1 0, h.1 1, h.2 (by decide)⟩
  · rintro ⟨h0, h1, h01⟩
    refine ⟨fun i => by fin_cases i <;> simpa, fun i j hij => ?_⟩
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · simpa using h01
    · simpa [real_inner_comm] using h01
    · exact absurd rfl hij

theorem inner_self_of_orthonormal {y : Fin 2 → W} (hy : Orthonormal ℝ y) (i : Fin 2) :
    ⟪y i, y i⟫_ℝ = 1 := by
  rw [real_inner_self_eq_norm_sq, hy.1 i, one_pow]

theorem inner_zero_one_of_orthonormal {y : Fin 2 → W} (hy : Orthonormal ℝ y) :
    ⟪y 0, y 1⟫_ℝ = 0 :=
  hy.2 (by decide)

theorem orthonormal_of_inner {y : Fin 2 → W} (h0 : ⟪y 0, y 0⟫_ℝ = 1) (h1 : ⟪y 1, y 1⟫_ℝ = 1)
    (h01 : ⟪y 0, y 1⟫_ℝ = 0) : Orthonormal ℝ y := by
  refine orthonormal_fin_two_iff.mpr ⟨?_, ?_, h01⟩
  · rw [real_inner_self_eq_norm_sq] at h0
    nlinarith [norm_nonneg (y 0)]
  · rw [real_inner_self_eq_norm_sq] at h1
    nlinarith [norm_nonneg (y 1)]

theorem orthonormal_planeRot {y : Fin 2 → W} (hy : Orthonormal ℝ y) (θ : ℝ) :
    Orthonormal ℝ (planeRot θ y) := by
  have h0 := inner_self_of_orthonormal hy 0
  have h1 := inner_self_of_orthonormal hy 1
  have h01 := inner_zero_one_of_orthonormal hy
  have h10 : ⟪y 1, y 0⟫_ℝ = 0 := by rw [real_inner_comm]; exact h01
  have hcs := Real.cos_sq_add_sin_sq θ
  refine orthonormal_of_inner ?_ ?_ ?_ <;>
  · simp only [planeRot_zero', planeRot_one', inner_add_left, inner_add_right, inner_smul_left,
      inner_smul_right, h0, h1, h01, h10, RCLike.conj_to_real]
    nlinarith [hcs]

theorem orthonormal_planeFlip {y : Fin 2 → W} (hy : Orthonormal ℝ y) :
    Orthonormal ℝ (planeFlip y) := by
  refine orthonormal_of_inner ?_ ?_ ?_
  · simpa using inner_self_of_orthonormal hy 0
  · simpa using inner_self_of_orthonormal hy 1
  · simpa using inner_zero_one_of_orthonormal hy

theorem planeRot_zero_angle (y : Fin 2 → W) : planeRot 0 y = y := by
  funext i
  fin_cases i <;> simp

theorem planeRot_planeRot (α β : ℝ) (y : Fin 2 → W) :
    planeRot α (planeRot β y) = planeRot (β + α) y := by
  funext i
  fin_cases i
  · simp only [Fin.zero_eta, planeRot_zero', planeRot_one', smul_add, smul_smul, Real.cos_add,
      Real.sin_add]
    module
  · simp only [Fin.mk_one, planeRot_zero', planeRot_one', smul_add, smul_smul, Real.cos_add,
      Real.sin_add]
    module

theorem planeDet_planeFlip_left (x y : Fin 2 → W) :
    planeDet (planeFlip x) y = -planeDet x y := by
  simp only [planeDet, planeFlip_zero, planeFlip_one, inner_neg_left]
  ring

theorem planeDet_self {y : Fin 2 → W} (hy : Orthonormal ℝ y) : planeDet y y = 1 := by
  simp only [planeDet, inner_self_of_orthonormal hy, inner_zero_one_of_orthonormal hy]
  ring

/-- A linear map commutes with rotations of pairs. -/
theorem map_planeRot {W' : Type*} [NormedAddCommGroup W'] [InnerProductSpace ℝ W']
    (L : W →ₗ[ℝ] W') (θ : ℝ) (y : Fin 2 → W) :
    (fun i => L (planeRot θ y i)) = planeRot θ (fun i => L (y i)) := by
  funext i
  fin_cases i <;> simp

/-- Every point of the unit circle is `(cos θ, sin θ)`. -/
theorem exists_cos_sin_eq {a b : ℝ} (h : a ^ 2 + b ^ 2 = 1) :
    ∃ θ : ℝ, Real.cos θ = a ∧ Real.sin θ = b := by
  let z : ℂ := ⟨a, b⟩
  have hz : ‖z‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_mk]
    rw [show a * a + b * b = 1 by nlinarith [h], Real.sqrt_one]
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hz
    exact zero_ne_one hz
  exact ⟨Complex.arg z, by rw [Complex.cos_arg hz0, hz, div_one],
    by rw [Complex.sin_arg, hz, div_one]⟩

variable [FiniteDimensional ℝ W]

/-- Expansion of a vector in an orthonormal pair of a plane. -/
theorem eq_inner_smul_add_of_orthonormal (h2 : Module.finrank ℝ W = 2) {y : Fin 2 → W}
    (hy : Orthonormal ℝ y) (v : W) :
    v = ⟪y 0, v⟫_ℝ • y 0 + ⟪y 1, v⟫_ℝ • y 1 := by
  have hsp : Submodule.span ℝ (Set.range y) = ⊤ :=
    hy.linearIndependent.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, h2])
  let ob := OrthonormalBasis.mk hy hsp.ge
  have h := ob.sum_repr' v
  simp only [ob, OrthonormalBasis.coe_mk, Fin.sum_univ_two] at h
  exact h.symm

/-- The first vector of an orthonormal pair has unit coordinates in another orthonormal pair. -/
theorem inner_sq_add_inner_sq_eq_one (h2 : Module.finrank ℝ W = 2) {x y : Fin 2 → W}
    (hx : Orthonormal ℝ x) (hy : Orthonormal ℝ y) :
    ⟪x 0, y 0⟫_ℝ ^ 2 + ⟪x 0, y 1⟫_ℝ ^ 2 = 1 := by
  have e0 := eq_inner_smul_add_of_orthonormal h2 hy (x 0)
  have hx0 := inner_self_of_orthonormal hx 0
  have hy0 := inner_self_of_orthonormal hy 0
  have hy1 := inner_self_of_orthonormal hy 1
  have hy01 := inner_zero_one_of_orthonormal hy
  have hy10 : ⟪y 1, y 0⟫_ℝ = 0 := by rw [real_inner_comm]; exact hy01
  rw [e0] at hx0
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, hy0, hy1,
    hy01, hy10, RCLike.conj_to_real] at hx0
  rw [real_inner_comm (y 0) (x 0), real_inner_comm (y 1) (x 0)]
  nlinarith [hx0]

theorem planeDet_sq_eq_one (h2 : Module.finrank ℝ W = 2) {x y : Fin 2 → W}
    (hx : Orthonormal ℝ x) (hy : Orthonormal ℝ y) : planeDet x y ^ 2 = 1 := by
  have e0 := eq_inner_smul_add_of_orthonormal h2 hy (x 0)
  have e1 := eq_inner_smul_add_of_orthonormal h2 hy (x 1)
  have hx0 := inner_self_of_orthonormal hx 0
  have hx1 := inner_self_of_orthonormal hx 1
  have hx01 := inner_zero_one_of_orthonormal hx
  have hy0 := inner_self_of_orthonormal hy 0
  have hy1 := inner_self_of_orthonormal hy 1
  have hy01 := inner_zero_one_of_orthonormal hy
  have hy10 : ⟪y 1, y 0⟫_ℝ = 0 := by rw [real_inner_comm]; exact hy01
  set a := ⟪y 0, x 0⟫_ℝ
  set b := ⟪y 1, x 0⟫_ℝ
  set c := ⟪y 0, x 1⟫_ℝ
  set d := ⟪y 1, x 1⟫_ℝ
  have q0 : a ^ 2 + b ^ 2 = 1 := by
    rw [e0] at hx0
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, hy0, hy1,
      hy01, hy10, RCLike.conj_to_real] at hx0
    nlinarith [hx0]
  have q1 : c ^ 2 + d ^ 2 = 1 := by
    rw [e1] at hx1
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, hy0, hy1,
      hy01, hy10, RCLike.conj_to_real] at hx1
    nlinarith [hx1]
  have q01 : a * c + b * d = 0 := by
    rw [e0, e1] at hx01
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, hy0, hy1,
      hy01, hy10, RCLike.conj_to_real] at hx01
    nlinarith [hx01]
  have hdet : planeDet x y = a * d - b * c := by
    simp only [planeDet, a, b, c, d, real_inner_comm]
  rw [hdet]
  nlinarith [q0, q1, q01]

theorem planeDet_ne_zero (h2 : Module.finrank ℝ W = 2) {x y : Fin 2 → W}
    (hx : Orthonormal ℝ x) (hy : Orthonormal ℝ y) : planeDet x y ≠ 0 := by
  intro h
  have := planeDet_sq_eq_one h2 hx hy
  rw [h] at this
  norm_num at this

/-- An orthonormal pair `x` with positive orientation determinant against `y` is a rotation of
`y`. -/
theorem eq_planeRot_of_planeDet_pos (h2 : Module.finrank ℝ W = 2) {x y : Fin 2 → W}
    (hx : Orthonormal ℝ x) (hy : Orthonormal ℝ y) (hd : 0 < planeDet x y) {θ : ℝ}
    (hc : Real.cos θ = ⟪x 0, y 0⟫_ℝ) (hs : Real.sin θ = ⟪x 0, y 1⟫_ℝ) :
    x = planeRot θ y := by
  have e0 := eq_inner_smul_add_of_orthonormal h2 hy (x 0)
  have e1 := eq_inner_smul_add_of_orthonormal h2 hy (x 1)
  have hx0 := inner_self_of_orthonormal hx 0
  have hx1 := inner_self_of_orthonormal hx 1
  have hx01 := inner_zero_one_of_orthonormal hx
  have hy0 := inner_self_of_orthonormal hy 0
  have hy1 := inner_self_of_orthonormal hy 1
  have hy01 := inner_zero_one_of_orthonormal hy
  have hy10 : ⟪y 1, y 0⟫_ℝ = 0 := by rw [real_inner_comm]; exact hy01
  have hsq := planeDet_sq_eq_one h2 hx hy
  set a := ⟪y 0, x 0⟫_ℝ with ha
  set b := ⟪y 1, x 0⟫_ℝ with hb
  set c := ⟪y 0, x 1⟫_ℝ with hc'
  set d := ⟪y 1, x 1⟫_ℝ with hd'
  have q0 : a ^ 2 + b ^ 2 = 1 := by
    rw [e0] at hx0
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, hy0, hy1,
      hy01, hy10, RCLike.conj_to_real] at hx0
    nlinarith [hx0]
  have q01 : a * c + b * d = 0 := by
    rw [e0, e1] at hx01
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, hy0, hy1,
      hy01, hy10, RCLike.conj_to_real] at hx01
    nlinarith [hx01]
  have hdet : planeDet x y = a * d - b * c := by
    simp only [planeDet, a, b, c, d, real_inner_comm]
  rw [hdet] at hd hsq
  have hone : a * d - b * c = 1 := by
    have h' : (a * d - b * c - 1) * (a * d - b * c + 1) = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp h' with h | h
    · linarith
    · linarith
  have hcb : c = -b := by linear_combination (-c) * q0 + a * q01 - b * hone
  have hda : d = a := by linear_combination (-d) * q0 + b * q01 + a * hone
  have hca : Real.cos θ = a := by rw [hc, real_inner_comm]
  have hsb : Real.sin θ = b := by rw [hs, real_inner_comm]
  funext i
  fin_cases i
  · simp only [Fin.zero_eta, planeRot_zero', hca, hsb]
    exact e0
  · simp only [Fin.mk_one, planeRot_one', hca, hsb]
    rw [e1, hcb, hda, neg_smul]

end DifferentialGeometry.Topology.VectorBundle
