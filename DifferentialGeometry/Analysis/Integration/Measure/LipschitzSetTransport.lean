/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Analysis.Integration.Measure.SmoothNullImage
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory
open scoped NNReal

namespace DifferentialGeometry.Analysis

/-- A map Lipschitz on the actual common buffer preserves AE equality of
contained planar sets. No injectivity or global extension is required. -/
theorem ae_eq_image_of_lipschitzOn
    {f : ℂ → ℂ} {B s t : Set ℂ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f B) (hs : s ⊆ B) (ht : t ⊆ B)
    (hst : s =ᵐ[volume] t) : f '' s =ᵐ[volume] f '' t := by
  have hdiff (A D : Set ℂ) (hA : A ⊆ B) (hAD : A =ᵐ[volume] D) :
      volume (f '' A \ f '' D) = 0 := by
    have hae : ∀ᵐ x : ℂ, x ∉ A \ D := by
      filter_upwards [hAD] with x hx
      exact fun h => h.2 (hx.mp h.1)
    have hn : volume (A \ D) = 0 := by
      have hn' := ae_iff.mp hae
      change volume {x : ℂ | ¬ (x ∉ A \ D)} = 0 at hn'
      have heq : {x : ℂ | ¬ (x ∉ A \ D)} = A \ D := by
        ext x
        simp only [Set.mem_ofPred_eq, not_not]
      rw [heq] at hn'
      exact hn'
    have himage := volume_image_eq_zero_of_lipschitzOn
      (hf.mono (sdiff_subset.trans hA)) hn
    apply measure_mono_null _ himage
    rintro _ ⟨⟨x, hx, rfl⟩, hxD⟩
    exact ⟨x, ⟨hx, fun h => hxD ⟨x, h, rfl⟩⟩, rfl⟩
  have hst' : ∀ᵐ y : ℂ, y ∉ f '' s \ f '' t := by
    apply ae_iff.mpr
    change volume {y : ℂ | ¬ (y ∉ f '' s \ f '' t)} = 0
    have heq : {y : ℂ | ¬ (y ∉ f '' s \ f '' t)} = f '' s \ f '' t := by
      ext y
      simp only [Set.mem_ofPred_eq, not_not]
    rw [heq]
    exact hdiff s t hs hst
  have hts' : ∀ᵐ y : ℂ, y ∉ f '' t \ f '' s := by
    apply ae_iff.mpr
    change volume {y : ℂ | ¬ (y ∉ f '' t \ f '' s)} = 0
    have heq : {y : ℂ | ¬ (y ∉ f '' t \ f '' s)} = f '' t \ f '' s := by
      ext y
      simp only [Set.mem_ofPred_eq, not_not]
    rw [heq]
    exact hdiff t s ht hst.symm
  filter_upwards [hst', hts'] with y hst_y hts_y
  apply propext
  constructor
  · intro hy
    by_contra hn
    exact hst_y ⟨hy, hn⟩
  · intro hy
    by_contra hn
    exact hts_y ⟨hy, hn⟩

/-- Transport an actual AE cell cover through a map Lipschitz on its buffer.
The index family need not be finite or countable. -/
theorem image_iUnion_ae_eq_of_lipschitzOn
    {ι : Type*} {f : ℂ → ℂ} {B P : Set ℂ} {s : ι → Set ℂ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f B) (hP : P ⊆ B)
    (hs : ∀ i, s i ⊆ P) (hcover : (⋃ i, s i) =ᵐ[volume] P) :
    (⋃ i, f '' s i) =ᵐ[volume] f '' P := by
  rw [← image_iUnion]
  exact ae_eq_image_of_lipschitzOn hf ((iUnion_subset hs).trans hP) hP hcover

end DifferentialGeometry.Analysis
