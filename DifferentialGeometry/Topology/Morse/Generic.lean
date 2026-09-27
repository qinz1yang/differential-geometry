/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
import DifferentialGeometry.External.TauCeti.Analysis.Calculus.Morse.Generic
import DifferentialGeometry.Topology.Morse.CriticalSet
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Topology.Morse

open Function _root_.MeasureTheory _root_.MeasureTheory.Measure Set

private theorem isNondegenerateCriticalPointAt_of_injective_fderiv
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (hcrit : fderiv ℝ f x = 0)
    (hinj : Injective (fderiv ℝ (fderiv ℝ f) x)) :
    IsNondegenerateCriticalPointAt 𝓘(ℝ, E) f x := by
  have hsymm : ∀ u v, chartHessianBilinAt f x u v = chartHessianBilinAt f x v u := by
    intro u v
    exact (hf.isSymmSndFDerivAt (by norm_num [minSmoothness])).eq u v
  have hB : QuadraticMap.associated (R := ℝ) (chartHessianAt f x) =
      chartHessianBilinAt f x := QuadraticMap.associated_left_inverse ℝ hsymm
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

private theorem forall_isNondegenerateCriticalPointAt_sub_of_bijective
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U)
    (a : E →L[ℝ] ℝ)
    (ha : ∀ x ∈ U, fderiv ℝ (fun y => f y - a y) x = 0 →
      Bijective (fderiv ℝ (fderiv ℝ fun y => f y - a y) x)) :
    ∀ x ∈ U, IsCriticalPointAt 𝓘(ℝ, E) (fun y => f y - a y) x →
      IsNondegenerateCriticalPointAt 𝓘(ℝ, E) (fun y => f y - a y) x := by
  intro x hx hcrit
  have hc : fderiv ℝ (fun y => f y - a y) x = 0 := by
    change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun y => f y - a y) x = 0 at hcrit
    rw [mfderiv_eq_fderiv] at hcrit
    exact hcrit
  exact isNondegenerateCriticalPointAt_of_injective_fderiv
    ((hf.contDiffAt (hU.mem_nhds hx)).sub a.contDiff.contDiffAt) hc (ha x hx hc).1

theorem ae_forall_isNondegenerateCriticalPointAt_sub
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace (E →L[ℝ] ℝ)] [BorelSpace (E →L[ℝ] ℝ)]
    (ν : Measure (E →L[ℝ] ℝ)) [IsAddHaarMeasure ν]
    {f : E → ℝ} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) :
    ∀ᵐ a ∂ν, ∀ x ∈ U, IsCriticalPointAt 𝓘(ℝ, E) (fun y => f y - a y) x →
      IsNondegenerateCriticalPointAt 𝓘(ℝ, E) (fun y => f y - a y) x := by
  filter_upwards [TauCeti.ae_forall_bijective_fderiv_fderiv_sub ν hU hf] with a ha
  exact forall_isNondegenerateCriticalPointAt_sub_of_bijective hU hf a ha

theorem dense_forall_isNondegenerateCriticalPointAt_sub
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E → ℝ} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) :
    Dense {a : E →L[ℝ] ℝ | ∀ x ∈ U,
      IsCriticalPointAt 𝓘(ℝ, E) (fun y => f y - a y) x →
        IsNondegenerateCriticalPointAt 𝓘(ℝ, E) (fun y => f y - a y) x} := by
  apply (TauCeti.dense_forall_bijective_fderiv_fderiv_sub hU hf).mono
  intro a ha
  exact forall_isNondegenerateCriticalPointAt_sub_of_bijective hU hf a ha

theorem exists_norm_lt_forall_isNondegenerateCriticalPointAt_sub
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E → ℝ} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : E →L[ℝ] ℝ, ‖a‖ < ε ∧ ∀ x ∈ U,
      IsCriticalPointAt 𝓘(ℝ, E) (fun y => f y - a y) x →
        IsNondegenerateCriticalPointAt 𝓘(ℝ, E) (fun y => f y - a y) x := by
  obtain ⟨a, ha, hgood⟩ := TauCeti.exists_norm_lt_forall_bijective_fderiv_fderiv_sub hU hf hε
  exact ⟨a, ha, forall_isNondegenerateCriticalPointAt_sub_of_bijective hU hf a hgood⟩

end DifferentialGeometry.Topology.Morse
