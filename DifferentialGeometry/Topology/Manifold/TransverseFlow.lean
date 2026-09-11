/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import DifferentialGeometry.Topology.Manifold.TransverseDerivative
import DifferentialGeometry.Topology.Manifold.InverseFunction
import DifferentialGeometry.Analysis.ODE.Flow.CompactSupport

set_option autoImplicit false

open Bundle Function Manifold Set Topology
open scoped Manifold ContDiff

noncomputable section

namespace DifferentialGeometry.Topology.SmoothEmbeddingRealNormalAtlas

open DifferentialGeometry.Analysis.ODE

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {G : Type*} [TopologicalSpace G]
    {B : Type*} [TopologicalSpace B] [ChartedSpace H B]
    {A : Type*} [TopologicalSpace A] [ChartedSpace G A] [T2Space A]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    [I.Boundaryless] [J.Boundaryless] [IsManifold I ∞ B] [IsManifold J ∞ A]
    {f : B → A}

set_option backward.isDefEq.respectTransparency false in
theorem isLocalDiffeomorphAt_flowMap
    (C : SmoothEmbeddingRealNormalAtlas I J ∞ f)
    (hdim : Module.finrank ℝ F = Module.finrank ℝ E + 1)
    (v : ∀ a : A, TangentSpace J a)
    (hv : ContMDiff J J.tangent ∞ (fun a ↦ (⟨a, v a⟩ : TangentBundle J A)))
    (hsupp : HasCompactSupport v) (x : B)
    (htrans : v (f x) ∉ range (mfderiv I J f x)) :
    IsLocalDiffeomorphAt (I.prod (modelWithCornersSelf ℝ ℝ)) J ∞
      (fun p : B × ℝ ↦
        curveAt v (exists_globalIntegralCurve_of_compactSupport v hv hsupp) (f p.1) p.2)
      (x, 0) := by
  let hc := exists_globalIntegralCurve_of_compactSupport v hv hsupp
  let Φ : B × ℝ → A := fun p ↦ curveAt v hc (f p.1) p.2
  let IP := I.prod (modelWithCornersSelf ℝ ℝ)
  have hΦ : ContMDiff IP J ∞ Φ :=
    (contMDiff_globalFlow_joint_of_compactSupport v hv hsupp).comp
      (contMDiff_snd.prodMk (C.contMDiff.comp contMDiff_fst))
  have hzero : (fun y : B ↦ Φ (y, 0)) = f := by
    funext y
    exact curveAt_zero v hc (f y)
  have htime : mfderiv (modelWithCornersSelf ℝ ℝ) J (fun t : ℝ ↦ Φ (x, t)) 0 =
      (1 : ℝ →L[ℝ] ℝ).smulRight (v (f x)) := by
    have h := (curveAt_integralCurve v hc (f x) 0).mfderiv
    rw [curveAt_zero v hc (f x)] at h
    exact h
  let L := C.transverseEquivAt (by simp) hdim x (v (f x)) htrans
  have hderiv : mfderiv IP J Φ (x, 0) = L.toContinuousLinearMap := by
    ext p
    rw [mfderiv_prod_eq_add_apply ((hΦ (x, 0)).mdifferentiableAt (by simp))]
    rw [hzero, htime]
    exact (C.transverseEquivAt_apply (by simp) hdim x (v (f x)) htrans p).symm
  exact isLocalDiffeomorphAt_of_contMDiffOn_of_isInvertible_mfderiv
    isOpen_univ (mem_univ _) hΦ.contMDiffOn ⟨L, hderiv.symm⟩

end DifferentialGeometry.Topology.SmoothEmbeddingRealNormalAtlas
