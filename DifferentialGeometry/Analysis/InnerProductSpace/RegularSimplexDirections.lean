import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring


set_option autoImplicit false

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace EuclideanSpace

def regularSimplexVector (m : ℕ) (i : Fin (m + 1)) : EuclideanSpace ℝ (Fin (m + 1)) :=
  Real.sqrt (((m : ℝ) + 1) / m) •
    (PiLp.single 2 i 1 - ((m : ℝ) + 1)⁻¹ • WithLp.toLp 2 (fun _ => (1 : ℝ)))

private theorem inner_centered_simplex (m : ℕ) (i j : Fin (m + 1)) :
    ⟪PiLp.single 2 i (1 : ℝ) - ((m : ℝ) + 1)⁻¹ • WithLp.toLp 2 (fun _ => (1 : ℝ)),
      PiLp.single 2 j (1 : ℝ) - ((m : ℝ) + 1)⁻¹ • WithLp.toLp 2 (fun _ => (1 : ℝ))⟫ =
      (if i = j then 1 else 0) - ((m : ℝ) + 1)⁻¹ := by
  have hn : (m : ℝ) + 1 ≠ 0 := by positivity
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, inner_smul_right]
  have hss : ⟪(PiLp.single 2 i (1 : ℝ) : EuclideanSpace ℝ (Fin (m + 1))),
      PiLp.single 2 j (1 : ℝ)⟫ = if i = j then 1 else 0 := by
    simp [PiLp.inner_apply]
  have hso (l : Fin (m + 1)) :
      ⟪(PiLp.single 2 l (1 : ℝ) : EuclideanSpace ℝ (Fin (m + 1))),
        WithLp.toLp 2 (fun _ => (1 : ℝ))⟫ = 1 := by
    simp [PiLp.inner_apply]
  have hos (l : Fin (m + 1)) :
      ⟪(WithLp.toLp 2 (fun _ => (1 : ℝ)) : EuclideanSpace ℝ (Fin (m + 1))),
        PiLp.single 2 l (1 : ℝ)⟫ = 1 := by
    simp [PiLp.inner_apply]
  have hoo : ⟪(WithLp.toLp 2 (fun _ => (1 : ℝ)) : EuclideanSpace ℝ (Fin (m + 1))),
      WithLp.toLp 2 (fun _ => (1 : ℝ))⟫ = (m : ℝ) + 1 := by
    rw [PiLp.inner_apply]
    simp
  rw [hss, hso, hos, hoo]
  field_simp
  ring

theorem inner_regularSimplexVector {m : ℕ} (hm : 0 < m) (i j : Fin (m + 1)) :
    ⟪regularSimplexVector m i, regularSimplexVector m j⟫ =
      if i = j then 1 else -(m : ℝ)⁻¹ := by
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have hn : (m : ℝ) + 1 ≠ 0 := by positivity
  rw [regularSimplexVector, regularSimplexVector, real_inner_smul_left, inner_smul_right,
    ← mul_assoc, ← pow_two, Real.sq_sqrt (by positivity), inner_centered_simplex]
  split_ifs <;> field_simp <;> ring

theorem norm_regularSimplexVector {m : ℕ} (hm : 0 < m) (i : Fin (m + 1)) :
    ‖regularSimplexVector m i‖ = 1 := by
  have hh := inner_regularSimplexVector hm i i
  simp only [ite_true, inner_self_eq_norm_sq_to_K, RCLike.ofReal_real_eq_id, id_eq] at hh
  nlinarith [norm_nonneg (regularSimplexVector m i)]

theorem sum_regularSimplexVector_coord (m : ℕ) (i : Fin (m + 1)) :
    ∑ j, regularSimplexVector m i j = 0 := by
  have hn : (m : ℝ) + 1 ≠ 0 := by positivity
  simp only [regularSimplexVector, PiLp.smul_apply, PiLp.sub_apply,
    smul_eq_mul]
  change ∑ j, Real.sqrt (((m : ℝ) + 1) / m) *
    ((PiLp.single 2 i (1 : ℝ) : EuclideanSpace ℝ (Fin (m + 1))) j - ((m : ℝ)+1)⁻¹ * 1) = 0
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  simp [PiLp.single_apply, hn]

theorem angle_regularSimplexVector {m : ℕ} (hm : 0 < m) {i j : Fin (m + 1)}
    (hij : i ≠ j) :
    InnerProductGeometry.angle (regularSimplexVector m i) (regularSimplexVector m j) =
      Real.pi / 2 + Real.arcsin ((m : ℝ)⁻¹) := by
  simp [InnerProductGeometry.angle, inner_regularSimplexVector hm, hij,
    norm_regularSimplexVector hm, Real.arccos, Real.arcsin_neg]

theorem regularSimplex_angle_margin {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    {i j : Fin (m + 1)} (hij : i ≠ j) :
    Real.pi / 2 + 8 * (8 * (n : ℝ))⁻¹ ≤
      InnerProductGeometry.angle (regularSimplexVector m i) (regularSimplexVector m j) := by
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hn' : 0 < (n : ℝ) := lt_of_lt_of_le hm' hmn'
  have hminv : (m : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hm').mpr (by exact_mod_cast hm)
  have hnonneg : 0 ≤ (m : ℝ)⁻¹ := le_of_lt (inv_pos.mpr hm')
  have hsin := Real.sin_le (Real.arcsin_nonneg.mpr hnonneg)
  rw [Real.sin_arcsin (by linarith) hminv] at hsin
  have hinv : (n : ℝ)⁻¹ ≤ (m : ℝ)⁻¹ := (inv_le_inv₀ hn' hm').mpr hmn'
  have hscale : 8 * (8 * (n : ℝ))⁻¹ = (n : ℝ)⁻¹ := by ring
  rw [hscale, angle_regularSimplexVector hm hij]
  linarith

theorem exists_regularSimplex {m : ℕ} (hm : 0 < m) :
    ∃ v : Fin (m + 1) → EuclideanSpace ℝ (Fin m),
      (∀ i, ‖v i‖ = 1) ∧
      (∀ i j, ⟪v i, v j⟫ = if i = j then 1 else -(m : ℝ)⁻¹) ∧
      (∀ i j, i ≠ j → InnerProductGeometry.angle (v i) (v j) =
        Real.pi / 2 + Real.arcsin ((m : ℝ)⁻¹)) := by
  let u : EuclideanSpace ℝ (Fin (m + 1)) := WithLp.toLp 2 (fun _ => (1 : ℝ))
  have hu : u ≠ 0 := by
    intro h
    have hh := congrArg (fun x : EuclideanSpace ℝ (Fin (m + 1)) => x 0) h
    norm_num [u] at hh
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) := ⟨by simp⟩
  let b := OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) m hu
  have hv (i : Fin (m + 1)) : regularSimplexVector m i ∈ (ℝ ∙ u)ᗮ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, PiLp.inner_apply]
    simpa [u] using sum_regularSimplexVector_coord m i
  let w (i : Fin (m + 1)) : (ℝ ∙ u)ᗮ := ⟨regularSimplexVector m i, hv i⟩
  refine ⟨fun i => b.repr (w i), ?_, ?_, ?_⟩
  · intro i
    rw [b.repr.norm_map]
    exact norm_regularSimplexVector hm i
  · intro i j
    rw [b.repr.inner_map_map]
    exact inner_regularSimplexVector hm i j
  · intro i j hij
    simp only [InnerProductGeometry.angle, b.repr.inner_map_map, b.repr.norm_map]
    exact angle_regularSimplexVector hm hij

theorem regularSimplex_perturbed_angle_margin {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    {i j : Fin (m + 1)} (hij : i ≠ j) {a b : EuclideanSpace ℝ (Fin (m + 1))}
    (ha : InnerProductGeometry.angle (regularSimplexVector m i) a < (8 * (n : ℝ))⁻¹)
    (hb : InnerProductGeometry.angle (regularSimplexVector m j) b < (8 * (n : ℝ))⁻¹) :
    Real.pi / 2 + 6 * (8 * (n : ℝ))⁻¹ < InnerProductGeometry.angle a b := by
  have hsep := regularSimplex_angle_margin hm hmn hij
  have h₁ := InnerProductGeometry.angle_le_angle_add_angle (regularSimplexVector m i) a
    (regularSimplexVector m j)
  have h₂ := InnerProductGeometry.angle_le_angle_add_angle a b (regularSimplexVector m j)
  rw [InnerProductGeometry.angle_comm b (regularSimplexVector m j)] at h₂
  linarith

end EuclideanSpace
