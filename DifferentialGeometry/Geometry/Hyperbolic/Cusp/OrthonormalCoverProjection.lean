/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.Hyperbolic.Cusp.FlatCoverProjection
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

set_option autoImplicit false
noncomputable section

open DifferentialGeometry GC.Endpoint
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.Geometry.Hyperbolic.HyperbolicCusp

theorem exists_torus_metric_frame (C : HyperbolicCusp) (p : Torus) :
    ∃ L : (Fin 2 → ℝ) ≃L[ℝ] TorusCoverVector,
      ∀ v w, C.torusMetric.inner p (L v) (L w) =
        v 0 * w 0 + v 1 * w 1 := by
  classical
  change ∃ L : (Fin 2 → ℝ) ≃L[ℝ] TangentSpace torusModel p,
    ∀ v w, C.torusMetric.inner p (L v) (L w) = v 0 * w 0 + v 1 * w 1
  obtain ⟨b, hb⟩ := Tensor0SBundle.exists_orthonormal_basis C.torusMetric p
  have hdim : Module.finrank ℝ (TangentSpace torusModel p) = 2 := by
    change Module.finrank ℝ TorusCoverVector = 2
    simp [TorusCoverVector]
  let B : Module.Basis (Fin 2) ℝ (TangentSpace torusModel p) := b.reindex (finCongr hdim)
  have hB (i j : Fin 2) : C.torusMetric.inner p (B i) (B j) =
      if i = j then (1 : ℝ) else 0 := by
    dsimp only [B]
    rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply, hb]
    simp
  let L : (Fin 2 → ℝ) ≃L[ℝ] TangentSpace torusModel p := B.equivFunL.symm
  have hL (v : Fin 2 → ℝ) : L v = v 0 • B 0 + v 1 • B 1 := by
    change B.equivFun.symm v = _
    rw [Module.Basis.equivFun_symm_apply, Fin.sum_univ_two]
  refine ⟨L, ?_⟩
  intro v w
  rw [hL v, hL w]
  simp [map_add, map_smul, add_apply, smul_apply, hB, smul_eq_mul]
  ring

theorem exists_orthonormal_cover_projection (C : HyperbolicCusp) :
    ∃ q : (Fin 2 → ℝ) → Torus,
      IsCoveringMap q ∧ Function.Surjective q ∧
      IsLocalDiffeomorph 𝓘(ℝ, Fin 2 → ℝ) torusModel ∞ q ∧
      ∀ (z v w : Fin 2 → ℝ),
        C.torusMetric.inner (q z)
            (mfderiv 𝓘(ℝ, Fin 2 → ℝ) torusModel q z v)
            (mfderiv 𝓘(ℝ, Fin 2 → ℝ) torusModel q z w) =
          v 0 * w 0 + v 1 * w 1 := by
  obtain ⟨p, q₀, hcover, hsurj, hlocal, hmetric⟩ := C.exists_flat_cover_projection
  obtain ⟨L, hL⟩ := C.exists_torus_metric_frame p
  let q : (Fin 2 → ℝ) → Torus := q₀ ∘ L
  refine ⟨q, hcover.comp_homeomorph L.toHomeomorph, hsurj.comp L.surjective,
    isLocalDiffeomorph_comp hlocal L.toDiffeomorph.isLocalDiffeomorph, ?_⟩
  intro z v w
  have hderiv (a : Fin 2 → ℝ) :
      mfderiv 𝓘(ℝ, Fin 2 → ℝ) torusModel q z a =
        mfderiv 𝓘(ℝ, TorusCoverVector) torusModel q₀ (L z) (L a) := by
    change mfderiv 𝓘(ℝ, Fin 2 → ℝ) torusModel (q₀ ∘ L) z a = _
    have hLd := (L.hasFDerivAt (x := z)).hasMFDerivAt
    rw [mfderiv_comp_apply z
      (hlocal.contMDiff.mdifferentiable (by decide) (L z)) hLd.mdifferentiableAt a,
      hLd.mfderiv]
    rfl
  exact (congrArg₂
    (fun (a b : TangentSpace torusModel (q z)) => C.torusMetric.inner (q z) a b)
    (hderiv v) (hderiv w)).trans ((hmetric (L z) (L v) (L w)).trans (hL v w))

end DifferentialGeometry.Geometry.Hyperbolic.HyperbolicCusp
