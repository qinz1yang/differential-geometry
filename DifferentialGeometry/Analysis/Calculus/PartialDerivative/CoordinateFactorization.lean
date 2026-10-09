/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open RealInnerProductSpace InnerProductSpace Filter
open scoped Topology

namespace DifferentialGeometry.LiouvilleIntegration


noncomputable section

variable {m : ℕ}

theorem coord_expand (v : EuclideanSpace ℝ (Fin m)) :
    ∑ i : Fin m, (v i) • (EuclideanSpace.basisFun (Fin m) ℝ i) = v := by
  calc ∑ i : Fin m, (v i) • (EuclideanSpace.basisFun (Fin m) ℝ i)
      = ∑ i : Fin m, ((EuclideanSpace.basisFun (Fin m) ℝ).repr v i) •
          (EuclideanSpace.basisFun (Fin m) ℝ i) :=
        Finset.sum_congr rfl (fun i _ => by rw [EuclideanSpace.basisFun_repr])
    _ = v := (EuclideanSpace.basisFun (Fin m) ℝ).sum_repr v

theorem fderiv_apply_eq_zero_of_off_partial
    {g : EuclideanSpace ℝ (Fin m) → ℝ} {U : Set (EuclideanSpace ℝ (Fin m))}
    {k : Fin m}
    (hzero : ∀ z ∈ U, ∀ j : Fin m, j ≠ k →
      fderiv ℝ g z (EuclideanSpace.basisFun (Fin m) ℝ j) = 0)
    {y : EuclideanSpace ℝ (Fin m)} (hy : y ∈ U)
    {v : EuclideanSpace ℝ (Fin m)} (hvk : v k = 0) :
    fderiv ℝ g y v = 0 := by
  conv_lhs => rw [← coord_expand v]
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [map_smul, smul_eq_mul]
  by_cases hik : i = k
  · subst hik; rw [hvk]; ring
  · rw [hzero y hy i hik]; ring

theorem hasDerivAt_affine (x v : EuclideanSpace ℝ (Fin m)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => x + s • v) v t := by
  have h1 : HasDerivAt (fun s : ℝ => s • v) v t := by
    have heq : (fun s : ℝ => s • v) = ⇑(ContinuousLinearMap.toSpanSingleton ℝ v) := by
      funext s; rw [ContinuousLinearMap.toSpanSingleton_apply]
    rw [heq]
    have h : HasDerivAt (⇑(ContinuousLinearMap.toSpanSingleton ℝ v))
        ((ContinuousLinearMap.toSpanSingleton ℝ v) 1) t :=
      (ContinuousLinearMap.toSpanSingleton ℝ v).hasDerivAt
    rwa [ContinuousLinearMap.toSpanSingleton_apply, one_smul] at h
  exact h1.const_add x

theorem apply_eq_of_off_partial_eq_zero
    {g : EuclideanSpace ℝ (Fin m) → ℝ} {U : Set (EuclideanSpace ℝ (Fin m))}
    (hUopen : IsOpen U) (hUconv : Convex ℝ U) (hdiff : DifferentiableOn ℝ g U)
    {k : Fin m}
    (hzero : ∀ z ∈ U, ∀ j : Fin m, j ≠ k →
      fderiv ℝ g z (EuclideanSpace.basisFun (Fin m) ℝ j) = 0)
    {x y : EuclideanSpace ℝ (Fin m)} (hx : x ∈ U) (hy : y ∈ U) (hk : x k = y k) :
    g x = g y := by
  have hvk : (y - x) k = 0 := by
    have h1 : (y - x) k = y k - x k := rfl
    rw [h1, hk, sub_self]
  have hseg : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → x + t • (y - x) ∈ U := by
    intro t ht
    have hcomb : x + t • (y - x) = (1 - t) • x + t • y := by module
    rw [hcomb]
    exact hUconv hx hy (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have hdiffφ : DifferentiableOn ℝ (g ∘ fun s : ℝ => x + s • (y - x)) (Set.Icc (0:ℝ) 1) := by
    have hLdiff : Differentiable ℝ (fun s : ℝ => x + s • (y - x)) :=
      fun t => (hasDerivAt_affine x (y - x) t).differentiableAt
    have hL : DifferentiableOn ℝ (fun s : ℝ => x + s • (y - x)) (Set.Icc (0:ℝ) 1) :=
      hLdiff.differentiableOn.mono (Set.subset_univ _)
    exact hdiff.comp hL (fun t ht => hseg t ht)
  have hderiv0 : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 →
      fderivWithin ℝ (g ∘ fun s : ℝ => x + s • (y - x)) (Set.Icc (0:ℝ) 1) t = 0 := by
    intro t ht
    have hmem : x + t • (y - x) ∈ U := hseg t ht
    have hgAt : DifferentiableAt ℝ g (x + t • (y - x)) :=
      hdiff.differentiableAt (hUopen.mem_nhds hmem)
    have hφAt : DifferentiableAt ℝ (g ∘ fun s : ℝ => x + s • (y - x)) t :=
      hgAt.comp t (hasDerivAt_affine x (y - x) t).differentiableAt
    have hudi : UniqueDiffWithinAt ℝ (Set.Icc (0:ℝ) 1) t :=
      uniqueDiffOn_Icc (by norm_num) t ht
    rw [hφAt.fderivWithin hudi, ← toSpanSingleton_deriv]
    have hder : HasDerivAt (g ∘ fun s : ℝ => x + s • (y - x))
        (fderiv ℝ g (x + t • (y - x)) (y - x)) t :=
      hgAt.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_affine x (y - x) t)
    have hc : fderiv ℝ g (x + t • (y - x)) (y - x) = 0 :=
      fderiv_apply_eq_zero_of_off_partial hzero hmem hvk
    rw [hc] at hder
    rw [hder.deriv]
    simp
  have hconst := (convex_Icc (0:ℝ) 1).is_const_of_fderivWithin_eq_zero hdiffφ hderiv0
    (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one)
  have h0 : (g ∘ fun s : ℝ => x + s • (y - x)) 0 = g x := by
    simp only [Function.comp_apply, zero_smul, add_zero]
  have h1y : (g ∘ fun s : ℝ => x + s • (y - x)) 1 = g y := by
    have hxy : x + (1:ℝ) • (y - x) = y := by module
    simp only [Function.comp_apply, hxy]
  rw [h0, h1y] at hconst
  exact hconst


end

end DifferentialGeometry.LiouvilleIntegration
