import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

noncomputable section

open Filter
open scoped BigOperators ContDiff Topology

namespace DifferentialGeometry.Analysis

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem fderiv_fderiv_sum_of_contDiffAt
    {κ : Type*} [Fintype κ] {f : κ → E → 𝕜} {x : E}
    (hf : ∀ k, ContDiffAt 𝕜 2 (f k) x) :
    fderiv 𝕜 (fderiv 𝕜 (fun y => ∑ k, f k y)) x =
      ∑ k, fderiv 𝕜 (fderiv 𝕜 (f k)) x := by
  classical
  have hnear : ∀ᶠ y in 𝓝 x, ∀ k, DifferentiableAt 𝕜 (f k) y := by
    rw [eventually_all]
    intro k
    filter_upwards [(hf k).eventually (by norm_num)] with y hy
    exact hy.differentiableAt (by norm_num)
  have hfirst : fderiv 𝕜 (fun y => ∑ k, f k y) =ᶠ[𝓝 x]
      fun y => ∑ k, fderiv 𝕜 (f k) y := by
    filter_upwards [hnear] with y hy
    exact fderiv_fun_sum fun k _ => hy k
  rw [hfirst.fderiv_eq]
  apply fderiv_fun_sum
  intro k _
  exact ((hf k).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)

theorem fderiv_fderiv_const_mul_of_contDiffAt
    {f : E → 𝕜} {x : E} (hf : ContDiffAt 𝕜 2 f x) (c : 𝕜) :
    fderiv 𝕜 (fderiv 𝕜 (fun y => c * f y)) x =
      c • fderiv 𝕜 (fderiv 𝕜 f) x := by
  have hfirst : fderiv 𝕜 (fun y => c * f y) =ᶠ[𝓝 x]
      fun y => c • fderiv 𝕜 f y := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    simpa only [smul_eq_mul] using
      fderiv_fun_const_smul (hy.differentiableAt (by norm_num)) c
  rw [hfirst.fderiv_eq]
  exact fderiv_fun_const_smul
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)) c

theorem sum_bilinear_apply_eq_basis
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : Module.Basis ι 𝕜 E) (T : κ → E →L[𝕜] E →L[𝕜] 𝕜) (v : κ → E) :
    (∑ k, T k (v k) (v k)) =
      ∑ i, ∑ j, ∑ k, (b.repr (v k) i * b.repr (v k) j) * T k (b i) (b j) := by
  classical
  have hexpand (k : κ) : T k (v k) (v k) =
      ∑ i, ∑ j, (b.repr (v k) i * b.repr (v k) j) * T k (b i) (b j) := by
    calc
      _ = T k (∑ i, b.repr (v k) i • b i) (∑ j, b.repr (v k) j • b j) := by
        rw [b.sum_repr]
      _ = _ := by
        simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul,
          Finset.mul_sum, mul_assoc]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
  simp only [hexpand]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_comm

theorem sum_fderiv_fderiv_apply_eq_basis
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : Module.Basis ι 𝕜 E) (v : κ → E) {f : κ → E → 𝕜} {x : E}
    (hf : ∀ k, ContDiffAt 𝕜 2 (f k) x) :
    (∑ k, fderiv 𝕜 (fderiv 𝕜 (f k)) x (v k) (v k)) =
      ∑ i, ∑ j, fderiv 𝕜 (fderiv 𝕜
        (fun y => ∑ k, (b.repr (v k) i * b.repr (v k) j) * f k y)) x (b i) (b j) := by
  classical
  rw [sum_bilinear_apply_eq_basis b]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [fderiv_fderiv_sum_of_contDiffAt
    (fun k => contDiffAt_const.mul (hf k))]
  simp only [sum_apply, fderiv_fderiv_const_mul_of_contDiffAt (hf _), smul_apply,
    smul_eq_mul]

theorem sum_fderiv_fderiv_apply_eq_of_rank_one
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : Module.Basis ι 𝕜 E) (v : κ → E)
    {A : E → ι → ι → 𝕜} {a : κ → E → 𝕜} {phi : E → 𝕜} {x : E}
    (hf : ∀ k, ContDiffAt 𝕜 2 (fun y => a k y * phi y) x)
    (hA : ∀ᶠ y in 𝓝 x, ∀ i j,
      A y i j = ∑ k, a k y * b.repr (v k) i * b.repr (v k) j) :
    (∑ k, fderiv 𝕜 (fderiv 𝕜 (fun y => a k y * phi y)) x (v k) (v k)) =
      ∑ i, ∑ j, fderiv 𝕜 (fderiv 𝕜 (fun y => A y i j * phi y)) x (b i) (b j) := by
  classical
  rw [sum_fderiv_fderiv_apply_eq_basis b v hf]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have heq : (fun y => ∑ k,
      (b.repr (v k) i * b.repr (v k) j) * (a k y * phi y)) =ᶠ[𝓝 x]
      fun y => A y i j * phi y := by
    filter_upwards [hA] with y hy
    rw [hy i j, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  exact congrArg (fun T : E →L[𝕜] E →L[𝕜] 𝕜 => T (b i) (b j))
    heq.fderiv.fderiv_eq

theorem fderiv_fderiv_apply_const_of_contDiffAt
    {f : E → 𝕜} {x : E} (hf : ContDiffAt 𝕜 2 f x) (v w : E) :
    fderiv 𝕜 (fun y => fderiv 𝕜 f y v) x w =
      fderiv 𝕜 (fderiv 𝕜 f) x w v := by
  let L : (E →L[𝕜] 𝕜) →L[𝕜] 𝕜 := ContinuousLinearMap.apply 𝕜 𝕜 v
  have hD : DifferentiableAt 𝕜 (fderiv 𝕜 f) x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
  change fderiv 𝕜 (L ∘ fderiv 𝕜 f) x w = _
  rw [fderiv_comp x L.differentiableAt hD, L.fderiv]
  rfl

theorem sum_directional_second_derivative_eq_of_rank_one
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : Module.Basis ι 𝕜 E) (v : κ → E)
    {A : E → ι → ι → 𝕜} {a : κ → E → 𝕜} {phi : E → 𝕜} {x : E}
    (hf : ∀ k, ContDiffAt 𝕜 2 (fun y => a k y * phi y) x)
    (hA : ∀ᶠ y in 𝓝 x, ∀ i j,
      A y i j = ∑ k, a k y * b.repr (v k) i * b.repr (v k) j) :
    (∑ k, fderiv 𝕜
      (fun y => fderiv 𝕜 (fun z => a k z * phi z) y (v k)) x (v k)) =
      ∑ i, ∑ j, fderiv 𝕜 (fderiv 𝕜 (fun y => A y i j * phi y)) x (b i) (b j) := by
  simp only [fderiv_fderiv_apply_const_of_contDiffAt (hf _)]
  exact sum_fderiv_fderiv_apply_eq_of_rank_one b v hf hA

end DifferentialGeometry.Analysis
