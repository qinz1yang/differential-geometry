/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
import DifferentialGeometry.External.TauCeti.Analysis.Calculus.Sard.EqualDimension
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.OpenPos

open scoped Topology ContDiff

namespace TauCeti

open Function MeasureTheory MeasureTheory.Measure Set

private theorem finrank_continuousLinearMap_real
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    Module.finrank ℝ E = Module.finrank ℝ (E →L[ℝ] ℝ) := by
  calc
    Module.finrank ℝ E = Module.finrank ℝ (Module.Dual ℝ E) :=
      Subspace.dual_finrank_eq.symm
    _ = Module.finrank ℝ (E →L[ℝ] ℝ) :=
      (LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)).finrank_eq

/-- **Almost every linear perturbation of a `C²` function is Morse.** For a Haar measure `ν` on
the continuous dual, for `ν`-almost every functional `a` the function `f - a` has only
nondegenerate critical points on the open set `U`.

The exceptional set is the set of critical values on `U` of the differential `fderiv ℝ f`, a map
between spaces of the same finite dimension, so it is null by the equal-dimensional case of
Sard's theorem.

Only the dual carries a measurable structure in the statement, since that is where `ν` lives; the
source `E` is measured only inside the proof, by Sard's lemma, and gets its Borel structure
there. -/
theorem ae_forall_bijective_fderiv_fderiv_sub
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace (E →L[ℝ] ℝ)] [BorelSpace (E →L[ℝ] ℝ)]
    (ν : Measure (E →L[ℝ] ℝ)) [IsAddHaarMeasure ν]
    {f : E → ℝ} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) :
    ∀ᵐ a ∂ν, ∀ x ∈ U, fderiv ℝ (fun y => f y - a y) x = 0 →
      Bijective (fderiv ℝ (fderiv ℝ fun y => f y - a y) x) := by
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
  have hfa : fderiv ℝ f x = a := sub_eq_zero.mp (h1.symm.trans hcrit)
  have hsurj : Surjective (fderiv ℝ (fderiv ℝ f) x) := by
    by_contra hn
    exact ha ⟨x, ⟨hx, hn⟩, hfa⟩
  have heq : (fderiv ℝ fun y => f y - a y) =ᶠ[nhds x] fun y => fderiv ℝ f y - a := by
    filter_upwards [hfx.eventually (by norm_num)] with y hy using by
      simpa using fderiv_fun_sub (hy.differentiableAt (by norm_num)) a.differentiableAt
  have h2 : fderiv ℝ (fderiv ℝ fun y => f y - a y) x = fderiv ℝ (fderiv ℝ f) x := by
    rw [heq.fderiv_eq, fderiv_sub_const]
  rw [h2]
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    finrank_continuousLinearMap_real).2 hsurj, hsurj⟩

/-- The linear perturbations that make a `C²` function Morse on an open set are dense in the
continuous dual. No measurable structure appears in the statement: the Haar measure that produces
the density is an auxiliary object of the proof, which installs the Borel structure it needs. -/
theorem dense_forall_bijective_fderiv_fderiv_sub
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E → ℝ} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) :
    Dense {a : E →L[ℝ] ℝ | ∀ x ∈ U,
      fderiv ℝ (fun y => f y - a y) x = 0 →
        Bijective (fderiv ℝ (fderiv ℝ fun y => f y - a y) x)} := by
  borelize (E →L[ℝ] ℝ)
  exact Measure.dense_of_ae
    (ae_forall_bijective_fderiv_fderiv_sub (addHaar : Measure (E →L[ℝ] ℝ)) hU hf)

/-- **A `C²` function is made Morse by an arbitrarily small linear perturbation**: for every
`ε > 0` there is a continuous linear functional of operator norm less than `ε` whose subtraction
leaves only nondegenerate critical points on `U`. -/
theorem exists_norm_lt_forall_bijective_fderiv_fderiv_sub
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E → ℝ} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : E →L[ℝ] ℝ, ‖a‖ < ε ∧ ∀ x ∈ U,
      fderiv ℝ (fun y => f y - a y) x = 0 →
        Bijective (fderiv ℝ (fderiv ℝ fun y => f y - a y) x) := by
  obtain ⟨a, ha, hball⟩ :=
    (dense_forall_bijective_fderiv_fderiv_sub hU hf).exists_mem_open
      Metric.isOpen_ball ⟨0, Metric.mem_ball_self hε⟩
  exact ⟨a, by simpa only [Metric.mem_ball, dist_zero_right] using hball, ha⟩

end TauCeti
