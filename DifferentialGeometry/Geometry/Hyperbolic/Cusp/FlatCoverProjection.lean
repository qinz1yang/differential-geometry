/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.Hyperbolic.Cusp.FlatUniversalCover
import DifferentialGeometry.Topology.Covering.Smooth.LocalDiffeomorph
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open

set_option autoImplicit false
noncomputable section

open DifferentialGeometry GC.Endpoint
open DifferentialGeometry.Geometry.Riemannian.Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Hyperbolic.HyperbolicCusp

abbrev TorusCoverVector :=
  EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)

theorem exists_flat_cover_projection (C : HyperbolicCusp) :
    ∃ (p₀ : Torus) (q : TorusCoverVector → Torus),
      IsCoveringMap q ∧ Function.Surjective q ∧
      IsLocalDiffeomorph 𝓘(ℝ, TorusCoverVector) torusModel ∞ q ∧
      ∀ (z : TorusCoverVector) (v w : TorusCoverVector),
        C.torusMetric.inner (q z)
            (mfderiv 𝓘(ℝ, TorusCoverVector) torusModel q z v)
            (mfderiv 𝓘(ℝ, TorusCoverVector) torusModel q z w) =
          C.torusMetric.inner p₀ v w := by
  let : LocallyPathConnectedSpace
      (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))) :=
    torusModel.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let : LocallyPathConnectedSpace Torus :=
    ChartedSpace.locallyPathConnectedSpace
      (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))) Torus
  let : SemilocallySimplyConnectedSpace Torus :=
    manifold_semilocallySimplyConnectedSpace (I := torusModel)
  let : Inhabited Torus := ⟨Classical.choice (inferInstance : Nonempty Torus)⟩
  obtain ⟨p, F, hF⟩ := C.torus_hasEuclideanUniversalCover
  let q : TorusCoverVector → Torus := UniversalCover.proj ∘ F
  have hcover : IsCoveringMap q :=
    UniversalCover.proj_isCoveringMap.comp_homeomorph F.toHomeomorph
  have hsurj : Function.Surjective q := by
    let : PathConnectedSpace Torus := PathConnectedSpace.of_locallyPathConnectedSpace
    intro x
    let x' : UniversalCover Torus :=
      ⟨x, ⟦PathConnectedSpace.somePath default x⟧⟩
    refine ⟨F.symm x', ?_⟩
    change UniversalCover.proj (F (F.symm x')) = x
    rw [F.apply_symm_apply]
    rfl
  have hlocal : IsLocalDiffeomorph 𝓘(ℝ, TorusCoverVector) torusModel ∞ q :=
    isLocalDiffeomorph_comp
      (UniversalCover.proj_localDiffeo (I := torusModel) (M := Torus))
      F.isLocalDiffeomorph
  refine ⟨UniversalCover.proj p, q, hcover, hsurj, hlocal, ?_⟩
  intro z v w
  have hderiv (a : TorusCoverVector) :
      mfderiv 𝓘(ℝ, TorusCoverVector) torusModel q z a =
        mfderiv 𝓘(ℝ, TorusCoverVector) torusModel F z a := by
    change mfderiv 𝓘(ℝ, TorusCoverVector) torusModel
      ((UniversalCover.proj : UniversalCover Torus → Torus) ∘ F) z a = _
    rw [mfderiv_comp_apply z
      (UniversalCover.hasMFDerivAt_proj (I := torusModel) (F z)).mdifferentiableAt
      (F.mdifferentiable (by decide) z) a,
      (UniversalCover.hasMFDerivAt_proj (I := torusModel) (F z)).mfderiv]
    rfl
  rw [hderiv v, hderiv w]
  exact hF z v w

end DifferentialGeometry.Geometry.Hyperbolic.HyperbolicCusp
