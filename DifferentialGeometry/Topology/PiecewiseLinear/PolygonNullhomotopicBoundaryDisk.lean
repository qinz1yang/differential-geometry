/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.NullMeridianComplementHomology
import DifferentialGeometry.Topology.PiecewiseLinear.PLDiskComplementHomology
import DifferentialGeometry.Topology.PiecewiseLinear.PolygonComplementHomology
import DifferentialGeometry.Topology.PiecewiseLinear.NonseparatingPolygonCarrier
import DifferentialGeometry.Topology.PiecewiseLinear.SolidTorusInteriorHomology

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private noncomputable def diskExclusionInclusion {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) :
    integralSingularHomology 1 A →ₗ[ℤ] integralSingularHomology 1 B :=
  integralSingularHomologyMap 1 ⟨inclusion hAB, continuous_inclusion hAB⟩

private theorem diskExclusionInclusion_comp {X : Type*} [TopologicalSpace X]
    {A B C : Set X} (hAB : A ⊆ B) (hBC : B ⊆ C)
    (a : integralSingularHomology 1 A) :
    diskExclusionInclusion hBC (diskExclusionInclusion hAB a) =
      diskExclusionInclusion (hAB.trans hBC) a := by
  change (integralSingularHomologyMap 1
    (⟨inclusion hBC, continuous_inclusion hBC⟩ : C(B, C))).comp
      (integralSingularHomologyMap 1
        (⟨inclusion hAB, continuous_inclusion hAB⟩ : C(A, B))) a = _
  rw [← integralSingularHomologyMap_comp]
  rfl

private theorem not_isPreconnected_of_disjoint_disk_firstHomology_carrier
    {S G Δ Z : Set (EuclideanSpace ℝ (Fin 3))}
    (hS : IsCombinatorialSolidTorus S) (hG : IsPLSphere 1 G)
    (hGS : G ⊆ frontier S) (hΔ : IsPLBall 2 Δ) (hGΔ : G ⊆ Δ)
    (hΔZ : Disjoint Δ Z) (hZ : Z.Nonempty) (hZS : Z ⊆ interior S)
    (hZgen : CarriesFundamentalGroupOnto Z S)
    (htriv : ∀ (hsub : G ⊆ S) (x : G) (g : FundamentalGroup G x),
      FundamentalGroup.map (⟨Set.inclusion hsub, continuous_inclusion hsub⟩ : C(G, S)) x g = 1) :
    ¬ IsPreconnected (frontier S \ G) := by
  intro hnonsep
  have hIG : interior S ⊆ Gᶜ := fun x hx hGx =>
    Set.disjoint_left.mp disjoint_interior_frontier hx (hGS hGx)
  have hZD : Z ⊆ Δᶜ := fun x hx hDx => Set.disjoint_left.mp hΔZ hDx hx
  have hDG : Δᶜ ⊆ Gᶜ := fun x hx hGx => hx (hGΔ hGx)
  have hcarry := hZgen.carriesFirstHomologyOnto hZ hS.1.isPathConnected
  have hZI : Function.Surjective (diskExclusionInclusion hZS) := by
    intro a
    obtain ⟨z, hz⟩ := hcarry.2 (hZS.trans interior_subset)
      (diskExclusionInclusion (interior_subset : interior S ⊆ S) a)
    refine ⟨z, hS.1.integralSingularHomologyMap_interior_injective ?_⟩
    change diskExclusionInclusion interior_subset (diskExclusionInclusion hZS z) = _
    rw [diskExclusionInclusion_comp]
    exact hz
  have hIC : Function.Surjective (diskExclusionInclusion hIG) :=
    TorusLinking.surjective_firstHomologyInclusion_of_nullhomotopic_meridian
      hS hG hGS hIG hnonsep htriv
  obtain ⟨ℓ⟩ := TorusLinking.nonempty_firstHomology_complement_addEquiv_int hG
  obtain ⟨a, ha⟩ := hIC (ℓ.symm 1)
  obtain ⟨z, hz⟩ := hZI a
  have hzero : diskExclusionInclusion (hZS.trans hIG) z = 0 := by
    change diskExclusionInclusion (hZD.trans hDG) z = 0
    rw [← diskExclusionInclusion_comp hZD hDG]
    have hD : diskExclusionInclusion hZD z = 0 :=
      (TorusLinking.subsingleton_firstHomology_complement_of_isPLDisk hΔ).elim _ _
    rw [hD, map_zero]
  have hvalue : diskExclusionInclusion (hZS.trans hIG) z = ℓ.symm 1 := by
    rw [← diskExclusionInclusion_comp hZS hIG, hz, ha]
  have hone : (1 : ℤ) = 0 := by
    have h := congrArg ℓ (hvalue.symm.trans hzero)
    simp at h
  exact one_ne_zero hone

theorem exists_isPLCell_frontier_of_polygon_nullhomotopic
    {S G Δ Z : Set (EuclideanSpace ℝ (Fin 3))} {r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)}
    (hS : IsCombinatorialSolidTorus S) (hGS : G ⊆ frontier S)
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ) (hGΔ : G = r '' stdSimplexBoundary 2)
    (hΔZ : Disjoint Δ Z) (hZ : Z.Nonempty) (hZS : Z ⊆ interior S)
    (hZgen : CarriesFundamentalGroupOnto Z S)
    (htriv : ∀ (hsub : G ⊆ S) (x : G) (g : FundamentalGroup G x),
      FundamentalGroup.map (⟨Set.inclusion hsub, continuous_inclusion hsub⟩ : C(G, S)) x g = 1) :
    ∃ (Δ' : Set (EuclideanSpace ℝ (Fin 3))) (r' : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)),
      IsPLHomeomorphOn r' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ' ∧ Δ' ⊆ frontier S ∧
        G = r' '' stdSimplexBoundary 2 := by
  have hG : IsPLSphere 1 G := hGΔ.symm ▸ hr.isPLSphere_image_stdSimplexBoundary
  have hGsub : G ⊆ Δ := by
    rw [hGΔ]
    exact (image_mono (fun _ hx => hx.1)).trans hr.image_eq.subset
  have hsep := not_isPreconnected_of_disjoint_disk_firstHomology_carrier hS hG hGS ⟨r, hr⟩
    hGsub hΔZ hZ hZS hZgen htriv
  exact hS.isPLTorus_frontier.exists_isPLHomeomorphOn_disk_of_not_isPreconnected_sdiff hG hGS hsep

end DifferentialGeometry.Topology.PiecewiseLinear
