import DifferentialGeometry.Topology.PiecewiseLinear.PLImage
import Mathlib.Analysis.InnerProductSpace.PiL2

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_affine_coordinates_of_linear_fiber {n : ℕ}
    (hdimE : Module.finrank ℝ E = n + 1) (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) (r : ℝ) :
    ∃ (e : EuclideanSpace ℝ (Fin n) →ᵃ[ℝ] E) (π : E →ₗ[ℝ] EuclideanSpace ℝ (Fin n)),
      Function.LeftInverse π e ∧ (∀ x, e (π x) = x ↔ ℓ x = r) ∧ (∀ y, ℓ (e y) = r) := by
  obtain ⟨u, hu⟩ := DFunLike.ne_iff.mp hℓ
  rw [LinearMap.zero_apply] at hu
  let v : E := (ℓ u)⁻¹ • u
  have hv : ℓ v = 1 := by simp only [v, map_smul, smul_eq_mul, inv_mul_cancel₀ hu]
  have hrange : LinearMap.range ℓ = ⊤ := LinearMap.range_eq_top.mpr fun c =>
    ⟨c • v, by rw [map_smul, hv, smul_eq_mul, mul_one]⟩
  have hdim : Module.finrank ℝ (LinearMap.ker ℓ) = n := by
    have h := LinearMap.finrank_range_add_finrank_ker ℓ
    rw [hrange, finrank_top, Module.finrank_self, hdimE] at h
    omega
  let P : E →ₗ[ℝ] LinearMap.ker ℓ :=
    { toFun := fun x => ⟨x - ℓ x • v, by
        rw [LinearMap.mem_ker, map_sub, map_smul, hv, smul_eq_mul, mul_one, sub_self]⟩
      map_add' := fun x y => by
        apply Subtype.ext
        change x + y - ℓ (x + y) • v = (x - ℓ x • v) + (y - ℓ y • v)
        rw [map_add, add_smul]
        abel
      map_smul' := fun c x => by
        apply Subtype.ext
        change c • x - ℓ (c • x) • v = c • (x - ℓ x • v)
        simp only [map_smul, smul_eq_mul, smul_sub, smul_smul] }
  let a : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] LinearMap.ker ℓ := LinearEquiv.ofFinrankEq _ _ (by
    simp only [finrank_euclideanSpace, Fintype.card_fin, hdim])
  let e : EuclideanSpace ℝ (Fin n) →ᵃ[ℝ] E :=
    ((LinearMap.ker ℓ).subtype.comp a.toLinearMap).toAffineMap +
      AffineMap.const ℝ (EuclideanSpace ℝ (Fin n)) (r • v)
  let π : E →ₗ[ℝ] EuclideanSpace ℝ (Fin n) := a.symm.toLinearMap.comp P
  have he (y : EuclideanSpace ℝ (Fin n)) : e y = (a y : E) + r • v := rfl
  have heheight : ∀ y, ℓ (e y) = r := by
    intro y
    rw [he, map_add, map_smul, hv, smul_eq_mul, mul_one,
      show ℓ (a y : E) = 0 from (a y).property, zero_add]
  have hPe (y : EuclideanSpace ℝ (Fin n)) : P (e y) = a y := by
    apply Subtype.ext
    change e y - ℓ (e y) • v = (a y : E)
    rw [heheight, he, add_sub_cancel_right]
  refine ⟨e, π, ?_, ?_, heheight⟩
  · intro y
    change a.symm (P (e y)) = y
    rw [hPe, a.symm_apply_apply]
  · intro x
    constructor
    · intro hx
      rw [← hx]
      exact heheight _
    · intro hx
      change (a (a.symm (P x)) : E) + r • v = x
      rw [a.apply_symm_apply]
      change x - ℓ x • v + r • v = x
      rw [hx, sub_add_cancel]


open Classical in
omit [FiniteDimensional ℝ E] in
theorem image_openSimplex_affineMap {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →ᵃ[ℝ] F) (s : Finset E) (hA : InjOn A (s : Set E)) :
    A '' openSimplex s = openSimplex (s.image A) := by
  classical
  ext y
  rw [mem_openSimplex_image_iff hA]
  constructor
  · rintro ⟨x, ⟨μ, hμ, hsum, hx⟩, rfl⟩
    refine ⟨μ, hμ, hsum, ?_⟩
    rw [← affineMap_apply_sum_smul A hsum, hx]
  · rintro ⟨μ, hμ, hsum, hy⟩
    refine ⟨∑ v ∈ s, μ v • v, ⟨μ, hμ, hsum, rfl⟩, ?_⟩
    rw [affineMap_apply_sum_smul A hsum]
    exact hy
end DifferentialGeometry.Topology.PiecewiseLinear
