/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
Coauthors: Jack McCarthy
-/
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional

/-!
# Composition operations for continuous multilinear maps

This file proves continuity and smoothness results for pre-composition of continuous multilinear
maps with a diagonal continuous linear map.

## Main results

* `ContinuousLinearMap.compContinuousMultilinearMapL_diag_continuous`: the map
  `p ↦ compContinuousLinearMapL (fun _ ↦ p)` is continuous (general domain/codomain).
* `ContinuousMultilinearMap.compContinuousLinearMapL_diag_continuous`: variant where
  pre-composition maps `F₁`-multilinear maps to `F₁`-multilinear maps.
* `ContinuousMultilinearMap.compContinuousLinearMapL_diag_contDiff`: the same map is `C^∞`.
-/

noncomputable section Comp

namespace ContinuousLinearMap

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  {M' : Type*} [NormedAddCommGroup M'] [NormedSpace 𝕜 M']
  {N : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N]
  {ι : Type*} [Finite ι]

/-- The map sending `p : M →L[𝕜] M'` to the operator `compContinuousLinearMapL (fun _ ↦ p)`
(pre-composing all `ι` slots of a continuous multilinear map with the same `p`) is continuous.
Used to prove continuity of pre-composition for alternating maps. -/
theorem compContinuousMultilinearMapL_diag_continuous :
    Continuous (fun p : M →L[𝕜] M' ↦
      (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : ι ↦ p) :
        ContinuousMultilinearMap 𝕜 (fun _ ↦ M') N →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ ↦ M) N))
  := by
  letI := Fintype.ofFinite ι
  let φ : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ M →L[𝕜] M') _ :=
    ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
    𝕜 (fun _ : ι ↦ M) (fun _ : ι ↦ M') N
  change Continuous (fun p : M →L[𝕜] M' ↦ φ (fun _ : ι ↦ p))
  exact φ.cont.comp (continuous_pi (fun _ ↦ continuous_id))

end ContinuousLinearMap

section Continuous

variable
  (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  (ι : Type*) [Finite ι]
  (F₁ F₂ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [ContinuousAdd F₁]

/-- The map sending `p : F₁ →L[𝕜] F₁` to the operator `compContinuousLinearMapL (fun _ ↦ p)`
(pre-composing all `ι` slots of a multilinear map with the same `p`) is continuous.
Used to prove `compContinuousLinearMapL_continuous` for alternating maps. -/
theorem ContinuousMultilinearMap.compContinuousLinearMapL_diag_continuous :
  Continuous (fun p : F₁ →L[𝕜] F₁ ↦
  (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : ι ↦ p) :
    ContinuousMultilinearMap 𝕜 (fun _ ↦ F₁) F₂ →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ ↦ F₁) F₂))
  := by
  letI := Fintype.ofFinite ι
  let φ : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁ →L[𝕜] F₁) _ :=
    ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
    𝕜 (fun _ : ι ↦ F₁) (fun _ : ι ↦ F₁) F₂
  change Continuous (fun p : F₁ →L[𝕜] F₁ ↦ φ (fun _ : ι ↦ p))
  apply Continuous.comp
  · apply ContinuousMultilinearMap.cont
  · apply continuous_pi
    intro _
    exact continuous_id

end Continuous

section Smooth
variable {𝕜 ι F₁ F₂} [NontriviallyNormedField 𝕜] [Fintype ι]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]

/-- The map sending `p : F₁ →L[𝕜] F₁` to `compContinuousLinearMapL (fun _ ↦ p)` is `C^∞`.
Does not require `CompleteSpace 𝕜`. Used to prove the smooth version for alternating maps. -/
theorem ContinuousMultilinearMap.compContinuousLinearMapL_diag_contDiff :
  ContDiff 𝕜 ⊤ (fun p : F₁ →L[𝕜] F₁ ↦
  (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : ι ↦ p) :
    ContinuousMultilinearMap 𝕜 (fun _ ↦ F₁) F₂ →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ ↦ F₁) F₂))
  := by
  letI domNACG : NormedAddCommGroup (F₁ →L[𝕜] F₁) :=
    ContinuousLinearMap.toNormedAddCommGroup
  letI domNS : NormedSpace 𝕜 (F₁ →L[𝕜] F₁) :=
    ContinuousLinearMap.toNormedSpace
  letI codNACG : NormedAddCommGroup
      (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂ →L[𝕜]
        ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂) :=
    ContinuousLinearMap.toNormedAddCommGroup
  letI codNS : NormedSpace 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂ →L[𝕜]
        ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂) :=
    ContinuousLinearMap.toNormedSpace
  let φ : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁ →L[𝕜] F₁) _ :=
    ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
    𝕜 (fun _ : ι ↦ F₁) (fun _ : ι ↦ F₁) F₂
  change ContDiff 𝕜 ⊤ (fun p : F₁ →L[𝕜] F₁ ↦ φ (fun _ : ι ↦ p))
  rw [show (fun p : F₁ →L[𝕜] F₁ => φ (fun _ : ι => p)) =
    (φ : (ι → (F₁ →L[𝕜] F₁)) → _) ∘ (fun p : F₁ →L[𝕜] F₁ => (fun _ : ι => p)) from rfl]
  exact (ContinuousMultilinearMap.contDiff φ).comp
    (contDiff_pi.2 (fun _ => contDiff_id))

end Smooth

end Comp
