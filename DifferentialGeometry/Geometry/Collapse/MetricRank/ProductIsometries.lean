import DifferentialGeometry.Geometry.Metric.L2Product
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Isometries between `L²` products (S-X144c, groups G10 / G11)

`HasEuclideanSplitting p k ε` uses the target `EuclideanSpace ℝ (Fin k) ×₂ Y`, while product
approximations in the rank kernels are into `ℝ ×₂ Z`, `ℝ² ×₂ Z`, `H ×₂ Z`. This file provides the
isometries that connect the two forms; nothing here is specific to Kleiner-Lott approximations.

* `prodCongrLeft_SMR e` : `A ≃ᵢ A'` gives `A ×₂ Z ≃ᵢ A' ×₂ Z` (`(a, z) ↦ (e a, z)`);
* `prodCongrRight_SMR e` : `Z ≃ᵢ Z'` gives `A ×₂ Z ≃ᵢ A ×₂ Z'`;
* `prodAssocIso_SMR` : `(A ×₂ B) ×₂ Z ≃ᵢ A ×₂ (B ×₂ Z)` (associativity, nested product);
* `realEuclideanOneIso_SMR` : `ℝ ≃ᵢ ℝ¹ = EuclideanSpace ℝ (Fin 1)`, `x ↦ !₂[x]`;
* `halfPlaneSplitIso_SMR` : the closed upper half plane `H = {v ∈ ℝ² | 0 ≤ v₁}` is isometric to
  `ℝ¹ ×₂ [0, ∞)`, `v ↦ (!₂[v₀], v₁)`.

In Mathlib (not used here): `IsometryEquiv.withLpUniqueProd` (`ℝ⁰ ×₂ Y ≃ᵢ Y`),
`IsometryEquiv.addRight`/`subRight` (translations), `WithLp.prod_dist_eq_add`; Mathlib has no
`L²`-product congruence, associativity or `ℝ ≃ᵢ ℝ¹`, so they are written here.
-/

set_option autoImplicit false

namespace GC.MetricGeometry

section Congr

variable {A A' Z Z' : Type*} [MetricSpace A] [MetricSpace A'] [MetricSpace Z] [MetricSpace Z']

/-- An isometry of the first factor induces an isometry of the `L²` product. -/
def prodCongrLeft_SMR (e : A ≃ᵢ A') : WithLp 2 (A × Z) ≃ᵢ WithLp 2 (A' × Z) where
  toFun w := WithLp.toLp 2 (e w.fst, w.snd)
  invFun w := WithLp.toLp 2 (e.symm w.fst, w.snd)
  left_inv w := by
    simp only [IsometryEquiv.symm_apply_apply, WithLp.toLp_fst, WithLp.toLp_snd]
    rfl
  right_inv w := by
    simp only [IsometryEquiv.apply_symm_apply, WithLp.toLp_fst, WithLp.toLp_snd]
    rfl
  isometry_toFun := by
    refine Isometry.of_dist_eq fun v w => ?_
    refine (sq_eq_sq₀ dist_nonneg dist_nonneg).mp ?_
    rw [WithLp.prod_dist_sq_eq_add_sq, WithLp.prod_dist_sq_eq_add_sq]
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, e.dist_eq]

theorem prodCongrLeft_apply_SMR (e : A ≃ᵢ A') (a : A) (z : Z) :
    prodCongrLeft_SMR e (WithLp.toLp 2 (a, z)) = WithLp.toLp 2 (e a, z) := rfl

/-- An isometry of the second factor induces an isometry of the `L²` product. -/
def prodCongrRight_SMR (e : Z ≃ᵢ Z') : WithLp 2 (A × Z) ≃ᵢ WithLp 2 (A × Z') where
  toFun w := WithLp.toLp 2 (w.fst, e w.snd)
  invFun w := WithLp.toLp 2 (w.fst, e.symm w.snd)
  left_inv w := by
    simp only [IsometryEquiv.symm_apply_apply, WithLp.toLp_fst, WithLp.toLp_snd]
    rfl
  right_inv w := by
    simp only [IsometryEquiv.apply_symm_apply, WithLp.toLp_fst, WithLp.toLp_snd]
    rfl
  isometry_toFun := by
    refine Isometry.of_dist_eq fun v w => ?_
    refine (sq_eq_sq₀ dist_nonneg dist_nonneg).mp ?_
    rw [WithLp.prod_dist_sq_eq_add_sq, WithLp.prod_dist_sq_eq_add_sq]
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, e.dist_eq]

theorem prodCongrRight_apply_SMR (e : Z ≃ᵢ Z') (a : A) (z : Z) :
    prodCongrRight_SMR (A := A) e (WithLp.toLp 2 (a, z)) = WithLp.toLp 2 (a, e z) := rfl

end Congr

section Assoc

variable {A B Z : Type*} [MetricSpace A] [MetricSpace B] [MetricSpace Z]

/-- **Associativity of the `L²` product**: `(A ×₂ B) ×₂ Z ≃ᵢ A ×₂ (B ×₂ Z)`. -/
def prodAssocIso_SMR :
    WithLp 2 (WithLp 2 (A × B) × Z) ≃ᵢ WithLp 2 (A × WithLp 2 (B × Z)) where
  toFun w := WithLp.toLp 2 (w.fst.fst, WithLp.toLp 2 (w.fst.snd, w.snd))
  invFun w := WithLp.toLp 2 (WithLp.toLp 2 (w.fst, w.snd.fst), w.snd.snd)
  left_inv w := rfl
  right_inv w := rfl
  isometry_toFun := by
    refine Isometry.of_dist_eq fun v w => ?_
    refine (sq_eq_sq₀ dist_nonneg dist_nonneg).mp ?_
    have h1 := WithLp.prod_dist_sq_eq_add_sq v w
    have h2 := WithLp.prod_dist_sq_eq_add_sq v.fst w.fst
    have h3 := WithLp.prod_dist_sq_eq_add_sq
      (WithLp.toLp 2 (v.fst.fst, WithLp.toLp 2 (v.fst.snd, v.snd)) :
        WithLp 2 (A × WithLp 2 (B × Z)))
      (WithLp.toLp 2 (w.fst.fst, WithLp.toLp 2 (w.fst.snd, w.snd)))
    have h4 := WithLp.prod_dist_sq_eq_add_sq
      (WithLp.toLp 2 (v.fst.snd, v.snd) : WithLp 2 (B × Z))
      (WithLp.toLp 2 (w.fst.snd, w.snd))
    simp only [WithLp.toLp_fst, WithLp.toLp_snd] at h3 h4
    rw [h3, h4, h1, h2]
    ring

end Assoc

section RealLine

/-- The line `ℝ` is isometric to `ℝ¹ = EuclideanSpace ℝ (Fin 1)`, `x ↦ !₂[x]`. -/
noncomputable def realEuclideanOneIso_SMR : ℝ ≃ᵢ EuclideanSpace ℝ (Fin 1) where
  toFun x := !₂[x]
  invFun v := v 0
  left_inv x := by simp
  right_inv v := by
    ext i
    fin_cases i
    simp
  isometry_toFun := by
    refine Isometry.of_dist_eq fun x y => ?_
    rw [EuclideanSpace.dist_eq]
    simp [Real.sqrt_sq_eq_abs, Real.dist_eq]

theorem realEuclideanOneIso_apply_SMR (x : ℝ) : realEuclideanOneIso_SMR x = !₂[x] := rfl

end RealLine

end GC.MetricGeometry
