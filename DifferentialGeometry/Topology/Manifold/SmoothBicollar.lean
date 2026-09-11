/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import DifferentialGeometry.Topology.Manifold.AmbientSectionExtension
import DifferentialGeometry.Topology.Manifold.TransverseFlow
import DifferentialGeometry.Topology.Manifold.CompactBicollar

set_option autoImplicit false

open Bundle Function Manifold Set Topology
open scoped Manifold ContDiff

noncomputable section

namespace DifferentialGeometry.Topology

open DifferentialGeometry.Analysis.ODE

theorem exists_smoothTwoSidedCollar_of_coorientedAtlas
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {G : Type*} [TopologicalSpace G]
    {B : Type*} [TopologicalSpace B] [ChartedSpace H B] [T2Space B] [CompactSpace B]
    {A : Type*} [TopologicalSpace A] [ChartedSpace G A] [T2Space A]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
    [I.Boundaryless] [J.Boundaryless] [IsManifold I ∞ B] [IsManifold J ∞ A]
    {f : B → A} (C : CoorientedSmoothEmbeddingRealNormalAtlas I J ∞ f)
    (hf : Injective f) (hdim : Module.finrank ℝ F = Module.finrank ℝ E + 1) :
    Nonempty (SmoothTwoSidedCollar I J f) := by
  obtain ⟨S, hsupp, _, htrans⟩ := C.exists_compactlySupported_transverseField hf
  let v : ∀ a : A, TangentSpace J a := S
  have hv : ContMDiff J J.tangent ∞ (fun a ↦ (⟨a, v a⟩ : TangentBundle J A)) := S.contMDiff
  let hc := exists_globalIntegralCurve_of_compactSupport v hv hsupp
  let Φ : B × ℝ → A := fun p ↦ curveAt v hc (f p.1) p.2
  have hΦ : ContMDiff (I.prod (modelWithCornersSelf ℝ ℝ)) J ∞ Φ :=
    (contMDiff_globalFlow_joint_of_compactSupport v hv hsupp).comp
      (contMDiff_snd.prodMk (C.toSmoothEmbeddingRealNormalAtlas.contMDiff.comp contMDiff_fst))
  apply exists_smoothTwoSidedCollar_of_localDiffeomorphAt_zero hf Φ hΦ.continuous
    (fun x ↦ curveAt_zero v hc (f x))
  intro x
  exact C.toSmoothEmbeddingRealNormalAtlas.isLocalDiffeomorphAt_flowMap
    hdim v hv hsupp x (htrans x)

theorem exists_smoothTwoSidedCollar_of_smoothSphereEmbedding
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ∞ M]
    (e : SphereTwo → M)
    (he : IsSmoothEmbedding
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ∞ e) :
    Nonempty (SmoothTwoSidedCollar
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) e) := by
  obtain ⟨C⟩ := nonempty_coorientedSmoothSphereEmbeddingRealNormalAtlas he
  exact exists_smoothTwoSidedCollar_of_coorientedAtlas C he.isEmbedding.injective (by simp)

end DifferentialGeometry.Topology
