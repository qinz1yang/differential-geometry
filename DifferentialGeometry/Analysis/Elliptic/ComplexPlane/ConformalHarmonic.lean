/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Calculus.Conformal.InnerProduct
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Separation.Hausdorff

/-!
# Harmonicity of a planar map conformal on a dense open set

Equal lengths and orthogonality of the derivative columns imply zero Laplacian
where a C² planar map is conformal. Continuity of the Laplacian extends this
identity across the complement of a dense open set.
-/

noncomputable section

open Set Filter InnerProductSpace
open scoped Topology ContDiff RealInnerProductSpace

namespace DifferentialGeometry.Analysis

private theorem laplacian_eq_zero_of_eventually_conformalAt
    {f : ℂ → ℂ} {x : ℂ} (hf : ContDiffAt ℝ 2 f x)
    (hc : ∀ᶠ y in 𝓝 x, ConformalAt f y) :
    Laplacian.laplacian f x = 0 := by
  let p : ℂ → ℂ := fun y => fderiv ℝ f y 1
  let q : ℂ → ℂ := fun y => fderiv ℝ f y Complex.I
  have hdd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hp : DifferentiableAt ℝ p x :=
    hdd.clm_apply (differentiableAt_const (1 : ℂ))
  have hq : DifferentiableAt ℝ q x :=
    hdd.clm_apply (differentiableAt_const Complex.I)
  have hlength : (fun y => ⟪p y, p y⟫_ℝ) =ᶠ[𝓝 x]
      (fun y => ⟪q y, q y⟫_ℝ) := by
    filter_upwards [hc] with y hy
    obtain ⟨c, _, hinner⟩ := conformalAt_iff'.mp hy
    change ⟪fderiv ℝ f y 1, fderiv ℝ f y 1⟫_ℝ =
      ⟪fderiv ℝ f y Complex.I, fderiv ℝ f y Complex.I⟫_ℝ
    rw [hinner 1 1, hinner Complex.I Complex.I]
    simp
  have horth : (fun y => ⟪p y, q y⟫_ℝ) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [hc] with y hy
    obtain ⟨c, _, hinner⟩ := conformalAt_iff'.mp hy
    change ⟪fderiv ℝ f y 1, fderiv ℝ f y Complex.I⟫_ℝ = 0
    rw [hinner 1 Complex.I]
    simp [Complex.inner]
  have hlengthDeriv (v : ℂ) :
      ⟪p x, fderiv ℝ p x v⟫_ℝ = ⟪q x, fderiv ℝ q x v⟫_ℝ := by
    have he := congrArg (fun L : ℂ →L[ℝ] ℝ => L v) hlength.fderiv_eq
    rw [fderiv_inner_apply ℝ hp hp, fderiv_inner_apply ℝ hq hq,
      real_inner_comm (p x) (fderiv ℝ p x v),
      real_inner_comm (q x) (fderiv ℝ q x v)] at he
    linarith
  have horthDeriv (v : ℂ) :
      ⟪p x, fderiv ℝ q x v⟫_ℝ + ⟪fderiv ℝ p x v, q x⟫_ℝ = 0 := by
    have he := congrArg (fun L : ℂ →L[ℝ] ℝ => L v) horth.fderiv_eq
    rw [fderiv_inner_apply ℝ hp hq, fderiv_const_apply] at he
    exact he
  have hcolumn (v w : ℂ) :
      fderiv ℝ (fun y => fderiv ℝ f y v) x w =
        fderiv ℝ (fderiv ℝ f) x w v := by
    rw [fderiv_clm_apply hdd (differentiableAt_const v)]
    simp
  have hmixed : fderiv ℝ p x Complex.I = fderiv ℝ q x 1 := by
    change fderiv ℝ (fun y => fderiv ℝ f y 1) x Complex.I =
      fderiv ℝ (fun y => fderiv ℝ f y Complex.I) x 1
    rw [hcolumn, hcolumn]
    exact (hf.isSymmSndFDerivAt (by norm_num)) Complex.I 1
  let L : ℂ := fderiv ℝ p x 1 + fderiv ℝ q x Complex.I
  have hpL : ⟪p x, L⟫_ℝ = 0 := by
    have hcross := horthDeriv Complex.I
    rw [hmixed, real_inner_comm (q x) (fderiv ℝ q x 1)] at hcross
    change ⟪p x, fderiv ℝ p x 1 + fderiv ℝ q x Complex.I⟫_ℝ = 0
    rw [inner_add_right]
    linarith [hlengthDeriv 1]
  have hqL : ⟪q x, L⟫_ℝ = 0 := by
    have hcross := horthDeriv 1
    rw [real_inner_comm (q x) (fderiv ℝ p x 1)] at hcross
    have hnorm := hlengthDeriv Complex.I
    rw [hmixed] at hnorm
    change ⟪q x, fderiv ℝ p x 1 + fderiv ℝ q x Complex.I⟫_ℝ = 0
    rw [inner_add_right]
    linarith
  have hsurj : Function.Surjective (fderiv ℝ f x) :=
    LinearMap.surjective_of_injective (f := (fderiv ℝ f x).toLinearMap)
      (conformalAt_iff_isConformalMap_fderiv.mp hc.self_of_nhds).injective
  obtain ⟨z, hz⟩ := hsurj L
  have hzsplit : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp
  have hspan : L = z.re • p x + z.im • q x := by
    calc
      L = fderiv ℝ f x z := hz.symm
      _ = fderiv ℝ f x (z.re • (1 : ℂ) + z.im • Complex.I) :=
        congrArg (fderiv ℝ f x) hzsplit
      _ = z.re • p x + z.im • q x := by
        simp only [ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul, p, q]
  have hLL : ⟪L, L⟫_ℝ = 0 := by
    calc
      ⟪L, L⟫_ℝ = ⟪z.re • p x + z.im • q x, L⟫_ℝ :=
        congrArg (fun v => ⟪v, L⟫_ℝ) hspan
      _ = 0 := by simp only [inner_add_left, real_inner_smul_left, hpL, hqL,
        mul_zero, add_zero]
  have hL : L = 0 := (inner_self_eq_zero (𝕜 := ℝ)).mp hLL
  calc
    Laplacian.laplacian f x =
        fderiv ℝ (fderiv ℝ f) x 1 1 +
          fderiv ℝ (fderiv ℝ f) x Complex.I Complex.I := by
      simp only [laplacian_eq_iteratedFDeriv_complexPlane, iteratedFDeriv_two_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one]
    _ = L := by simp only [L, p, q, hcolumn]
    _ = 0 := hL

/-- A C² planar map conformal on a dense open subset of an open set is harmonic
throughout that open set. No orientation choice is needed. -/
theorem harmonicOnNhd_of_contDiffOn_of_dense_conformalAt
    {f : ℂ → ℂ} {D Ω : Set ℂ}
    (hD : IsOpen D) (hΩ : IsOpen Ω) (hΩD : Ω ⊆ D)
    (hDense : D ⊆ closure Ω) (hf : ContDiffOn ℝ 2 f D)
    (hconf : ∀ z ∈ Ω, ConformalAt f z) :
    InnerProductSpace.HarmonicOnNhd f D := by
  have hzeroΩ (x : ℂ) (hx : x ∈ Ω) : Laplacian.laplacian f x = 0 := by
    apply laplacian_eq_zero_of_eventually_conformalAt
      ((hf x (hΩD hx)).contDiffAt (hD.mem_nhds (hΩD hx)))
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact hconf y hy
  have hzeroD (x : ℂ) (hx : x ∈ D) : Laplacian.laplacian f x = 0 := by
    have hzeroWithin : Laplacian.laplacian f =ᶠ[𝓝[Ω] x] (fun _ => (0 : ℂ)) := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact hzeroΩ y hy
    have hlimit : Tendsto (Laplacian.laplacian f) (𝓝[Ω] x)
        (𝓝 (Laplacian.laplacian f x)) :=
      ((hf x hx).contDiffAt (hD.mem_nhds hx)).continuousAt_laplacian.mono_left
        nhdsWithin_le_nhds
    have hzeroLimit : Tendsto (Laplacian.laplacian f) (𝓝[Ω] x) (𝓝 (0 : ℂ)) :=
      (tendsto_const_nhds : Tendsto (fun _ : ℂ => (0 : ℂ))
        (𝓝[Ω] x) (𝓝 (0 : ℂ))).congr' hzeroWithin.symm
    exact tendsto_nhds_unique' (mem_closure_iff_nhdsWithin_neBot.mp (hDense hx))
      hlimit hzeroLimit
  intro x hx
  refine ⟨(hf x hx).contDiffAt (hD.mem_nhds hx), ?_⟩
  filter_upwards [hD.mem_nhds hx] with y hy
  exact hzeroD y hy

end DifferentialGeometry.Analysis
