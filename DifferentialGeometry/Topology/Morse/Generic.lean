/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
import DifferentialGeometry.Analysis.Calculus.Sard
import DifferentialGeometry.Topology.Morse.CriticalSet
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Topology.Morse

open Function _root_.MeasureTheory _root_.MeasureTheory.Measure Set

private theorem finrank_continuousLinearMap_real
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    Module.finrank ℝ E = Module.finrank ℝ (E →L[ℝ] ℝ) := by
  calc
    Module.finrank ℝ E = Module.finrank ℝ (Module.Dual ℝ E) :=
      Subspace.dual_finrank_eq.symm
    _ = Module.finrank ℝ (E →L[ℝ] ℝ) :=
      (LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)).finrank_eq

private theorem isNondegenerateCriticalPointAt_of_surjective_fderiv
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (hcrit : fderiv ℝ f x = 0)
    (hsurj : Surjective (fderiv ℝ (fderiv ℝ f) x)) :
    IsNondegenerateCriticalPointAt 𝓘(ℝ, E) f x := by
  have hsymm : ∀ u v, chartHessianBilinAt f x u v = chartHessianBilinAt f x v u := by
    intro u v
    exact (hf.isSymmSndFDerivAt (by norm_num [minSmoothness])).eq u v
  have hB : QuadraticMap.associated (R := ℝ) (chartHessianAt f x) =
      chartHessianBilinAt f x := QuadraticMap.associated_left_inverse ℝ hsymm
  have hinj : Injective (fderiv ℝ (fderiv ℝ f) x) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      finrank_continuousLinearMap_real).2 hsurj
  refine ⟨?_, ?_⟩
  · change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x = 0
    rw [mfderiv_eq_fderiv]
    change fderiv ℝ f x = (0 : E →L[ℝ] ℝ)
    exact hcrit
  · change (QuadraticMap.associated (R := ℝ) (chartHessianAt f x)).SeparatingLeft
    rw [hB]
    intro u hu
    apply hinj
    apply ContinuousLinearMap.ext
    intro v
    simp only [map_zero, zero_apply]
    exact hu v

theorem ae_forall_isNondegenerateCriticalPointAt_sub
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace (E →L[ℝ] ℝ)] [BorelSpace (E →L[ℝ] ℝ)]
    (ν : Measure (E →L[ℝ] ℝ)) [IsAddHaarMeasure ν]
    {f : E → ℝ} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) :
    ∀ᵐ a ∂ν, ∀ x ∈ U, IsCriticalPointAt 𝓘(ℝ, E) (fun y => f y - a y) x →
      IsNondegenerateCriticalPointAt 𝓘(ℝ, E) (fun y => f y - a y) x := by
  have hdf : DifferentiableOn ℝ (fderiv ℝ f) U :=
    (hf.fderiv_of_isOpen (m := 1) hU (by norm_num)).differentiableOn one_ne_zero
  have hnull : ν (fderiv ℝ f '' {x ∈ U | ¬ Surjective (fderiv ℝ (fderiv ℝ f) x)}) = 0 := by
    refine addHaar_image_eq_zero_of_not_surjective_fderivWithin ν finrank_continuousLinearMap_real
      (fun y hy => ?_) (fun _ hy => hy.2)
    exact ((hdf y hy.1).differentiableAt (hU.mem_nhds hy.1)).hasFDerivAt.hasFDerivWithinAt
  have hgood : ∀ᵐ a ∂ν,
      a ∉ fderiv ℝ f '' {x ∈ U | ¬ Surjective (fderiv ℝ (fderiv ℝ f) x)} := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hnull
  filter_upwards [hgood] with a ha
  intro x hx hcrit
  have hfx : ContDiffAt ℝ 2 f x := hf.contDiffAt (hU.mem_nhds hx)
  have h1 : fderiv ℝ (fun y => f y - a y) x = fderiv ℝ f x - a := by
    simpa using fderiv_fun_sub (hfx.differentiableAt (by norm_num)) a.differentiableAt
  have hc : fderiv ℝ (fun y => f y - a y) x = 0 := by
    change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun y => f y - a y) x = 0 at hcrit
    rw [mfderiv_eq_fderiv] at hcrit
    change fderiv ℝ (fun y => f y - a y) x = (0 : E →L[ℝ] ℝ) at hcrit
    exact hcrit
  have hfa : fderiv ℝ f x = a := sub_eq_zero.mp (h1.symm.trans hc)
  have hsurj : Surjective (fderiv ℝ (fderiv ℝ f) x) := by
    by_contra hn
    exact ha ⟨x, ⟨hx, hn⟩, hfa⟩
  have heq : (fderiv ℝ fun y => f y - a y) =ᶠ[nhds x] fun y => fderiv ℝ f y - a := by
    filter_upwards [hfx.eventually (by norm_num)] with y hy using by
      simpa using fderiv_fun_sub (hy.differentiableAt (by norm_num)) a.differentiableAt
  have h2 : fderiv ℝ (fderiv ℝ fun y => f y - a y) x = fderiv ℝ (fderiv ℝ f) x := by
    rw [heq.fderiv_eq, fderiv_sub_const]
  apply isNondegenerateCriticalPointAt_of_surjective_fderiv
    (hfx.sub a.contDiff.contDiffAt) hc
  rwa [h2]

theorem dense_forall_isNondegenerateCriticalPointAt_sub
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E → ℝ} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) :
    Dense {a : E →L[ℝ] ℝ | ∀ x ∈ U,
      IsCriticalPointAt 𝓘(ℝ, E) (fun y => f y - a y) x →
        IsNondegenerateCriticalPointAt 𝓘(ℝ, E) (fun y => f y - a y) x} := by
  borelize (E →L[ℝ] ℝ)
  exact Measure.dense_of_ae
    (ae_forall_isNondegenerateCriticalPointAt_sub (addHaar : Measure (E →L[ℝ] ℝ)) hU hf)

theorem exists_norm_lt_forall_isNondegenerateCriticalPointAt_sub
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E → ℝ} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : E →L[ℝ] ℝ, ‖a‖ < ε ∧ ∀ x ∈ U,
      IsCriticalPointAt 𝓘(ℝ, E) (fun y => f y - a y) x →
        IsNondegenerateCriticalPointAt 𝓘(ℝ, E) (fun y => f y - a y) x := by
  obtain ⟨a, ha, hball⟩ :=
    (dense_forall_isNondegenerateCriticalPointAt_sub hU hf).exists_mem_open
      Metric.isOpen_ball ⟨0, Metric.mem_ball_self hε⟩
  exact ⟨a, by simpa only [Metric.mem_ball, dist_zero_right] using hball, ha⟩

end DifferentialGeometry.Topology.Morse
