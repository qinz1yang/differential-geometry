/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SmoothBoundaryPlane
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Atlas
import DifferentialGeometry.Geometry.Boundary.Manifold.Basic
import DifferentialGeometry.Geometry.Boundary.Model.EuclideanHalfSpace
import Mathlib.Geometry.Manifold.Instances.Sphere

open Set Topology Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.PiecewiseLinear

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

theorem inclEuclidean_three_eq_normalFirstEquiv (w : EuclideanSpace ℝ (Fin 2)) :
    EuclideanHalfSpaceInstance.inclEuclidean 3 w = normalFirstEquiv 2 (w, 0) := by
  have h := EuclideanHalfSpaceInstance.inclEuclideanCLM_succ_apply 2 w
  exact h

theorem isSmoothEmbedding_coe_of_boundary_openPartialHomeomorph
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] {N : Type*} [TopologicalSpace N]
    [ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 1)) ℝ) N]
    [IsManifold ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞ N]
    (F : OpenPartialHomeomorph N (BoundaryManifold (𝓡∂ 3) M)) (hFs : F.source = univ)
    (hF : ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ)) (HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)) ∞ F univ)
    (hFi : ContMDiffOn (HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞
      F.symm F.target) :
    IsSmoothEmbedding ((𝓡 1).prod 𝓘(ℝ, ℝ)) (𝓡∂ 3) ∞ (fun x => (F x : M)) := by
  classical
  let _ : Nonempty (HasSmoothBoundary.boundaryH (I := 𝓡∂ 3)) :=
    ⟨(0 : EuclideanSpace ℝ (Fin 2))⟩
  let Λ : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (EuclideanSpace ℝ (Fin 1) × ℝ) :=
    (normalFirstEquiv 1).symm
  have hI1 : ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × ℝ) ∞
      ((𝓡 1).prod 𝓘(ℝ, ℝ)) := ModelWithCorners.contMDiff _
  have hI2 : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × ℝ) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞
      ((𝓡 1).prod 𝓘(ℝ, ℝ)).symm := by
    have := ((𝓡 1).prod 𝓘(ℝ, ℝ)).contMDiffOn_symm (n := ∞)
    rwa [ModelWithCorners.range_eq_univ, contMDiffOn_univ] at this
  let Φ₀ : EuclideanSpace ℝ (Fin 2) ≃ₜ ModelProd (EuclideanSpace ℝ (Fin 1)) ℝ :=
    Λ.toHomeomorph.trans ((𝓡 1).prod 𝓘(ℝ, ℝ)).toHomeomorph.symm
  have hΦ₀app : ∀ w, Φ₀ w = ((𝓡 1).prod 𝓘(ℝ, ℝ)).symm (Λ w) := fun w => rfl
  have hΦ₀sapp : ∀ u, Φ₀.symm u = Λ.symm ((𝓡 1).prod 𝓘(ℝ, ℝ) u) := fun u => rfl
  have hΦ₀ : ContMDiff (HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞ Φ₀ :=
    (hI2.comp (Λ.contDiff.contMDiff (n := ∞))).congr fun w => (hΦ₀app w).symm
  have hΦ₀i : ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℝ)) (HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)) ∞
      Φ₀.symm :=
    ((Λ.symm.contDiff.contMDiff (n := ∞)).comp hI1).congr fun u => (hΦ₀sapp u).symm
  refine ⟨?_, IsEmbedding.subtypeVal.comp (F.isOpenEmbedding hFs).isEmbedding⟩
  apply IsImmersionOfComplement.isImmersion (F := ℝ)
  intro x
  set y := F x with hydef
  let b := chartAt (HasSmoothBoundary.boundaryH (I := 𝓡∂ 3)) y
  have hb : b ∈ IsManifold.maximalAtlas (HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)) ∞
      (BoundaryManifold (𝓡∂ 3) M) := IsManifold.chart_mem_maximalAtlas y
  have hbeq : b = BoundaryManifold.boundaryChart (I := 𝓡∂ 3) y :=
    BoundaryManifold.defaultBoundaryChart_eq_boundaryChart (I := 𝓡∂ 3) y
  let ψ := chartAt (EuclideanHalfSpace 3) (y : M)
  let α : OpenPartialHomeomorph N (ModelProd (EuclideanSpace ℝ (Fin 1)) ℝ) :=
    (F.trans b).transHomeomorph Φ₀
  have hαs : α.source = F.source ∩ F ⁻¹' b.source := by
    change (F.trans b).source = _
    rw [OpenPartialHomeomorph.trans_source]
  have hαt : ∀ u, u ∈ α.target ↔ Φ₀.symm u ∈ b.target ∧ b.symm (Φ₀.symm u) ∈ F.target := by
    intro u
    change Φ₀.symm u ∈ (F.trans b).target ↔ _
    rw [OpenPartialHomeomorph.trans_target]
    rfl
  have hxα : x ∈ α.source := by
    rw [hαs]
    exact ⟨hFs ▸ mem_univ x, mem_chart_source _ y⟩
  have hbsm : ContMDiffOn (HasSmoothBoundary.boundaryI (I := 𝓡∂ 3))
      (HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)) ∞ b b.source :=
    contMDiffOn_of_mem_maximalAtlas hb
  have hbsi : ContMDiffOn (HasSmoothBoundary.boundaryI (I := 𝓡∂ 3))
      (HasSmoothBoundary.boundaryI (I := 𝓡∂ 3)) ∞ b.symm b.target :=
    contMDiffOn_symm_of_mem_maximalAtlas hb
  have hαmax : α ∈ IsManifold.maximalAtlas ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞ N := by
    refine DifferentialGeometry.OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn α ?_ ?_
    · rw [hαs]
      exact hΦ₀.comp_contMDiffOn (hbsm.comp (hF.mono (subset_univ _)) fun z hz => hz.2)
    · exact hFi.comp (hbsi.comp hΦ₀i.contMDiffOn fun u hu => ((hαt u).mp hu).1)
        fun u hu => ((hαt u).mp hu).2
  have hψmax : ψ ∈ IsManifold.maximalAtlas (𝓡∂ 3) ∞ M := IsManifold.chart_mem_maximalAtlas _
  have hsrcM : ∀ p : BoundaryManifold (𝓡∂ 3) M, p ∈ b.source → (p : M) ∈ ψ.source := by
    intro p hp
    rw [hbeq] at hp
    exact hp
  refine IsImmersionAtOfComplement.mk_of_charts
    ((Λ.symm.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)).trans (normalFirstEquiv 2)) α ψ hxα
    (hsrcM y (mem_chart_source _ y)) hαmax hψmax (fun z hz => ?_) fun u hu => ?_
  · rw [hαs] at hz
    exact hsrcM _ hz.2
  · have hu' : ((𝓡 1).prod 𝓘(ℝ, ℝ)).symm u ∈ α.target := hu.2
    obtain ⟨hwb, hwF⟩ := (hαt _).mp hu'
    have hIu : (𝓡 1).prod 𝓘(ℝ, ℝ) (((𝓡 1).prod 𝓘(ℝ, ℝ)).symm u) = u :=
      ModelWithCorners.right_inv _ (by rw [ModelWithCorners.range_eq_univ]; exact mem_univ u)
    have hw : Φ₀.symm (((𝓡 1).prod 𝓘(ℝ, ℝ)).symm u) = Λ.symm u := by
      rw [hΦ₀sapp, hIu]
    rw [hw] at hwb hwF
    have hFeq : F (α.symm (((𝓡 1).prod 𝓘(ℝ, ℝ)).symm u)) = b.symm (Λ.symm u) := by
      change F (F.symm (b.symm (Φ₀.symm (((𝓡 1).prod 𝓘(ℝ, ℝ)).symm u)))) = _
      rw [hw, F.right_inv hwF]
    have hmemψ : ((b.symm (Λ.symm u) : BoundaryManifold (𝓡∂ 3) M) : M) ∈ ψ.source :=
      hsrcM _ (b.map_target hwb)
    have hincl := BoundaryManifold.inclH_boundaryChart_apply (I := 𝓡∂ 3) y
      (b.symm (Λ.symm u)) hmemψ
    rw [← hbeq, b.right_inv hwb] at hincl
    change (𝓡∂ 3) (ψ ((F (α.symm (((𝓡 1).prod 𝓘(ℝ, ℝ)).symm u)) : M))) =
      normalFirstEquiv 2 (Λ.symm u, 0)
    rw [hFeq, ← hincl]
    exact inclEuclidean_three_eq_normalFirstEquiv (Λ.symm u)

end DifferentialGeometry.Topology.PiecewiseLinear
