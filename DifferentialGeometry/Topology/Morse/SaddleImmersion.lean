/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Morse.SaddleSection

open Set Function
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Morse

namespace DifferentialGeometry.Morse

theorem saddleLevelPoint_mfderiv_injective {ε : ℝ} (hε : 0 < ε) (side : Bool) (s : ℝ) :
    Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, MorseModel 2) (saddleLevelPoint ε side) s) := by
  rw [mfderiv_eq_fderiv]
  change Injective (fderiv ℝ (saddleLevelPoint ε side) s)
  let L : MorseModel 2 →L[ℝ] ℝ := ContinuousLinearMap.proj 1
  have hA := (contDiff_saddleLevelPoint hε side).differentiable (by simp) s
  have hd : L.comp (fderiv ℝ (saddleLevelPoint ε side) s) = 1 := by
    have hh := (L.hasFDerivAt.comp s hA.hasFDerivAt).fderiv
    change fderiv ℝ (fun t : ℝ => t) s = L.comp (fderiv ℝ (saddleLevelPoint ε side) s) at hh
    exact hh.symm.trans (hasFDerivAt_id s).fderiv
  intro x y hxy
  have hh := congrArg L hxy
  change L.comp (fderiv ℝ (saddleLevelPoint ε side) s) x =
    L.comp (fderiv ℝ (saddleLevelPoint ε side) s) y at hh
  rw [hd] at hh
  exact hh

variable {H M : Type} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ (MorseModel 2) H}

theorem saddle_section_mfderiv_injective
    (χ : PartialDiffeomorph 𝓘(ℝ, MorseModel 2) I (MorseModel 2) M ∞)
    {ε s : ℝ} (hε : 0 < ε) (side : Bool) (hs : saddleLevelPoint ε side s ∈ χ.source) :
    Injective (mfderiv 𝓘(ℝ, ℝ) I (fun t => χ (saddleLevelPoint ε side t)) s) := by
  have hloc : IsLocalDiffeomorphAt 𝓘(ℝ, MorseModel 2) I ∞ χ
      (saddleLevelPoint ε side s) := ⟨χ, hs, eqOn_refl _ _⟩
  have hA := (contDiff_saddleLevelPoint hε side).contMDiff.mdifferentiableAt (x := s) (by simp)
  have hd : mfderiv 𝓘(ℝ, ℝ) I (fun t => χ (saddleLevelPoint ε side t)) s =
      (mfderiv 𝓘(ℝ, MorseModel 2) I χ (saddleLevelPoint ε side s)).comp
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, MorseModel 2) (saddleLevelPoint ε side) s) :=
    mfderiv_comp s (χ.mdifferentiableAt (by simp) hs) hA
  rw [hd]
  exact (hloc.mfderivToContinuousLinearEquiv (by simp)).injective.comp
    (saddleLevelPoint_mfderiv_injective hε side s)

end DifferentialGeometry.Morse
