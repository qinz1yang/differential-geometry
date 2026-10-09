/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Analysis.Calculus.MapConvergence.TransverseIntersection
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

set_option autoImplicit false
noncomputable section

open Set Filter Manifold
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Analysis

/-- A chartwise local C1 limit of injective maps into the actual manifold has
no transverse double point. Eventual containment in the common chart is an
explicit convergence input. No rank or injectivity of the limit is assumed. -/
theorem not_surjective_coprod_mfderiv_of_injective_c1_limit
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    {V : Set ℂ} (hV : IsOpen V) {u : ℕ → ℂ → M} {u₀ : ℂ → M}
    {a b : ℂ} (ha : a ∈ V) (hb : b ∈ V) (hab : a ≠ b) (heq : u₀ a = u₀ b)
    (hu : ∀ᶠ n in atTop, ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (u n) V)
    (hu₀ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 u₀ V)
    (hinj : ∀ᶠ n in atTop, Set.InjOn (u n) V)
    (hchart₀ : MapsTo u₀ V (extChartAt 𝓘(ℝ, E) (u₀ a)).source)
    (hchart : ∀ᶠ n in atTop,
      MapsTo (u n) V (extChartAt 𝓘(ℝ, E) (u₀ a)).source)
    (hval : ∀ z ∈ V, Tendsto
      (fun n => extChartAt 𝓘(ℝ, E) (u₀ a) (u n z)) atTop
      (𝓝 (extChartAt 𝓘(ℝ, E) (u₀ a) (u₀ z))))
    (hder : ∀ K : Set ℂ, IsCompact K → K ⊆ V →
      TendstoUniformlyOn
        (fun n z => fderiv ℝ (fun w => extChartAt 𝓘(ℝ, E) (u₀ a) (u n w)) z)
        (fun z => fderiv ℝ (fun w => extChartAt 𝓘(ℝ, E) (u₀ a) (u₀ w)) z)
        atTop K) :
    ¬ Function.Surjective
      ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u₀ a).coprod
        (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u₀ b))) := by
  let : FiniteDimensional ℝ ℂ := Complex.basisOneI.finiteDimensional_of_finite
  let χ := extChartAt 𝓘(ℝ, E) (u₀ a)
  let X : ℕ → ℂ → E := fun n z => χ (u n z)
  let X₀ : ℂ → E := fun z => χ (u₀ z)
  have hχ (p : M) (hp : p ∈ χ.source) :
      ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) 1 χ p := by
    have hsm : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ χ p :=
      contMDiffAt_extChartAt' (by simpa only [χ, extChartAt_source] using hp)
    exact hsm.of_le (by simp)
  have hX₀ : ContDiffOn ℝ 1 X₀ V := by
    intro z hz
    exact ((hχ (u₀ z) (hchart₀ hz)).comp z
      (hu₀.contMDiffAt (hV.mem_nhds hz))).contDiffAt.contDiffWithinAt
  have hX : ∀ᶠ n in atTop, DifferentiableOn ℝ (X n) V := by
    filter_upwards [hu, hchart] with n hn hnc
    have hsm : ContDiffOn ℝ 1 (X n) V := by
      intro z hz
      exact ((hχ (u n z) (hnc hz)).comp z
        (hn.contMDiffAt (hV.mem_nhds hz))).contDiffAt.contDiffWithinAt
    exact hsm.differentiableOn (by simp)
  have hXinj : ∀ᶠ n in atTop, Set.InjOn (X n) V := by
    filter_upwards [hinj, hchart] with n hn hnc
    intro z hz w hw hzw
    exact hn hz hw (χ.injOn (hnc hz) (hnc hw) hzw)
  have hnot := not_surjective_coprod_fderiv_of_injective_c1_limit
    hV hX hX₀ hXinj hval hder ha hb hab (congrArg χ heq)
  let D (z : ℂ) : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u₀ z
  let C (z : ℂ) : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) χ (u₀ z)
  have hchain (z : ℂ) (hz : z ∈ V) (v : ℂ) :
      fderiv ℝ X₀ z v = C z (D z v) := by
    have hh := mfderiv_comp_apply z
      ((hχ (u₀ z) (hchart₀ hz)).mdifferentiableAt (by simp))
      ((hu₀.contMDiffAt (hV.mem_nhds hz)).mdifferentiableAt (by simp)) v
    rw [mfderiv_eq_fderiv] at hh
    exact hh
  have hCa : (C a).IsInvertible :=
    isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ, E)) (hchart₀ ha)
  have hCb : C b = C a :=
    congrArg (fun p : M =>
      (show E →L[ℝ] E from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) χ p)) heq.symm
  intro hsurj
  apply hnot
  intro y
  obtain ⟨w, hw⟩ := hCa.surjective y
  obtain ⟨z, hz⟩ := hsurj w
  refine ⟨z, ?_⟩
  change fderiv ℝ X₀ a z.1 + -(fderiv ℝ X₀ b z.2) = y
  rw [hchain a ha, hchain b hb, hCb, ← map_neg, ← map_add]
  exact (congrArg (C a) hz).trans hw

end DifferentialGeometry.Analysis
