import Mathlib.Algebra.Module.BigOperators
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Tactic.Ring

open scoped BigOperators Topology

namespace DifferentialGeometry.Analysis.Calculus

theorem sum_fderiv_mul_eq_of_rank_one_coefficients
    {𝕜 E ι κ : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Fintype ι]
    (e : Module.Basis ι 𝕜 E) (s : Finset κ) (a : κ → E → 𝕜) (v : κ → E)
    (C : ι → ι → E → 𝕜) (x : E) (df : E →L[𝕜] 𝕜)
    (ha : ∀ k ∈ s, DifferentiableAt 𝕜 (a k) x)
    (hC : ∀ i j, C i j =ᶠ[𝓝 x]
      fun y => ∑ k ∈ s, a k y * e.repr (v k) i * e.repr (v k) j) :
    (∑ i, ∑ j, fderiv 𝕜 (C i j) x (e i) * df (e j)) =
      ∑ k ∈ s, fderiv 𝕜 (a k) x (v k) * df (v k) := by
  have hderiv (i j : ι) (z : E) :
      fderiv 𝕜 (C i j) x z = ∑ k ∈ s,
        fderiv 𝕜 (a k) x z * e.repr (v k) i * e.repr (v k) j := by
    have hsum : HasFDerivAt
        (fun y => ∑ k ∈ s, a k y * e.repr (v k) i * e.repr (v k) j)
        (∑ k ∈ s, e.repr (v k) j •
          (e.repr (v k) i • fderiv 𝕜 (a k) x)) x := by
      exact HasFDerivAt.fun_sum fun k hk =>
        ((ha k hk).hasFDerivAt.mul_const (e.repr (v k) i)).mul_const
          (e.repr (v k) j)
    rw [(hsum.congr_of_eventuallyEq (hC i j)).fderiv]
    simp only [sum_apply, smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hrepr (l : E →L[𝕜] 𝕜) (z : E) :
      (∑ i, e.repr z i * l (e i)) = l z := by
    simpa only [map_sum, map_smul, smul_eq_mul] using congrArg l (e.sum_repr z)
  calc
    (∑ i, ∑ j, fderiv 𝕜 (C i j) x (e i) * df (e j)) =
        ∑ i, ∑ j, ∑ k ∈ s,
          (fderiv 𝕜 (a k) x (e i) * e.repr (v k) i * e.repr (v k) j) *
            df (e j) := by
      simp_rw [hderiv, Finset.sum_mul]
    _ = ∑ k ∈ s, ∑ i, ∑ j,
        (fderiv 𝕜 (a k) x (e i) * e.repr (v k) i * e.repr (v k) j) *
          df (e j) := Finset.sum_comm_cycle
    _ = ∑ k ∈ s,
        (∑ i, e.repr (v k) i * fderiv 𝕜 (a k) x (e i)) *
          (∑ j, e.repr (v k) j * df (e j)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ k ∈ s, fderiv 𝕜 (a k) x (v k) * df (v k) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hrepr, hrepr]

end DifferentialGeometry.Analysis.Calculus
