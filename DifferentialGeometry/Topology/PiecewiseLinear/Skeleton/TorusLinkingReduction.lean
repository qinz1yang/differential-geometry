/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.FirstHomologyCarrying
import DifferentialGeometry.Topology.PiecewiseLinear.NonseparatingPolygonCarrier

/-!
# Integer linking and meridian exclusion

This reconnaissance reduction retains the parametrized boundary-disk endpoint of Section 31.
Four unreviewed leaves remain: integer homology of a polygon complement, vanishing first homology
of a PL disk complement, injectivity for the interior inclusion of a solid torus, and the
surjective complement map of a nonseparating null meridian. The carrying and vanishing diagrams
and the endpoint assembly are proved. No claim of a completed linking theory is made.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear.TorusLinking

noncomputable def firstHomologyInclusion {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) :
    integralSingularHomology 1 A →ₗ[ℤ] integralSingularHomology 1 B :=
  integralSingularHomologyMap 1 ⟨inclusion hAB, continuous_inclusion hAB⟩

theorem firstHomologyInclusion_comp {X : Type*} [TopologicalSpace X]
    {A B C : Set X} (hAB : A ⊆ B) (hBC : B ⊆ C)
    (a : integralSingularHomology 1 A) :
    firstHomologyInclusion hBC (firstHomologyInclusion hAB a) =
      firstHomologyInclusion (hAB.trans hBC) a := by
  change (integralSingularHomologyMap 1
    (⟨inclusion hBC, continuous_inclusion hBC⟩ : C(B, C))).comp
      (integralSingularHomologyMap 1
        (⟨inclusion hAB, continuous_inclusion hAB⟩ : C(A, B))) a = _
  rw [← integralSingularHomologyMap_comp]
  rfl

theorem surjective_firstHomologyInclusion_of_carries_of_injective
    {X : Type*} [TopologicalSpace X] {Z A S : Set X}
    (hZA : Z ⊆ A) (hAS : A ⊆ S) (hcarry : CarriesFirstHomologyOnto Z S)
    (hinj : Function.Injective (firstHomologyInclusion hAS)) :
    Function.Surjective (firstHomologyInclusion hZA) := by
  intro a
  obtain ⟨z, hz⟩ := hcarry.2 (hZA.trans hAS) (firstHomologyInclusion hAS a)
  refine ⟨z, hinj ?_⟩
  rw [firstHomologyInclusion_comp]
  exact hz

theorem firstHomologyInclusion_eq_zero_of_factorization
    {X : Type*} [TopologicalSpace X] {Z A B : Set X}
    (hZA : Z ⊆ A) (hAB : A ⊆ B)
    (hzero : Subsingleton (integralSingularHomology 1 A))
    (z : integralSingularHomology 1 Z) :
    firstHomologyInclusion (hZA.trans hAB) z = 0 := by
  rw [← firstHomologyInclusion_comp hZA hAB]
  have hz : firstHomologyInclusion hZA z = 0 := hzero.elim _ _
  rw [hz, map_zero]

theorem exists_integer_linking_equiv_of_isPLSphere
    {G : Set (EuclideanSpace ℝ (Fin 3))} (hG : IsPLSphere 1 G) :
    Nonempty (integralSingularHomology 1 (Gᶜ : Set (EuclideanSpace ℝ (Fin 3))) ≃+ ℤ) := by
  sorry

theorem subsingleton_firstHomology_complement_of_isPLBall
    {Δ : Set (EuclideanSpace ℝ (Fin 3))} (hΔ : IsPLBall 2 Δ) :
    Subsingleton (integralSingularHomology 1 (Δᶜ : Set (EuclideanSpace ℝ (Fin 3)))) := by
  sorry

theorem injective_firstHomologyInclusion_interior_solidTorus
    {S : Set (EuclideanSpace ℝ (Fin 3))} (hS : IsTopologicalSolidTorus S) :
    Function.Injective (firstHomologyInclusion (interior_subset : interior S ⊆ S)) := by
  sorry

theorem surjective_firstHomologyInclusion_complement_of_null_meridian
    {S G : Set (EuclideanSpace ℝ (Fin 3))}
    (hS : IsCombinatorialSolidTorus S) (hG : IsPLSphere 1 G)
    (hGS : G ⊆ frontier S) (hIG : interior S ⊆ Gᶜ)
    (hnonsep : IsPreconnected (frontier S \ G))
    (htriv : ∀ (hsub : G ⊆ S) (x : G) (g : FundamentalGroup G x),
      FundamentalGroup.map (⟨Set.inclusion hsub, continuous_inclusion hsub⟩ : C(G, S)) x g = 1) :
    Function.Surjective (firstHomologyInclusion hIG) := by
  sorry

theorem not_isPreconnected_sdiff_of_disjoint_disk_and_carrier
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
  have hZI := surjective_firstHomologyInclusion_of_carries_of_injective hZS interior_subset
    hcarry (injective_firstHomologyInclusion_interior_solidTorus hS.1)
  have hIC := surjective_firstHomologyInclusion_complement_of_null_meridian
    hS hG hGS hIG hnonsep htriv
  obtain ⟨ℓ⟩ := exists_integer_linking_equiv_of_isPLSphere hG
  obtain ⟨a, ha⟩ := hIC (ℓ.symm 1)
  obtain ⟨z, hz⟩ := hZI a
  have hzero : firstHomologyInclusion (hZS.trans hIG) z = 0 :=
    firstHomologyInclusion_eq_zero_of_factorization hZD hDG
      (subsingleton_firstHomology_complement_of_isPLBall hΔ) z
  have hvalue : firstHomologyInclusion (hZS.trans hIG) z = ℓ.symm 1 := by
    rw [← firstHomologyInclusion_comp hZS hIG, hz, ha]
  have hone : (1 : ℤ) = 0 := by
    have h := congrArg ℓ (hvalue.symm.trans hzero)
    simp at h
  exact one_ne_zero hone

theorem exists_isPLCell_frontier_of_polygon_nullhomotopic
    {S G Δ Z : Set (EuclideanSpace ℝ (Fin 3))} {r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)}
    (hS : IsCombinatorialSolidTorus S) (hGS : G ⊆ frontier S)
    (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) Δ) (hGΔ : G = r '' stdSimplexBoundary 2)
    (hΔZ : Disjoint Δ Z) (hZ : Z.Nonempty) (hZS : Z ⊆ interior S)
    (hZgen : CarriesFundamentalGroupOnto Z S)
    (htriv : ∀ (hsub : G ⊆ S) (x : G) (g : FundamentalGroup G x),
      FundamentalGroup.map (⟨Set.inclusion hsub, continuous_inclusion hsub⟩ : C(G, S)) x g = 1) :
    ∃ (Δ' : Set (EuclideanSpace ℝ (Fin 3))) (r' : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)),
      IsPLHomeomorphOn r' (stdSimplex ℝ (Fin 3)) Δ' ∧ Δ' ⊆ frontier S ∧
        G = r' '' stdSimplexBoundary 2 := by
  have hG : IsPLSphere 1 G := hGΔ.symm ▸ hr.isPLSphere_image_stdSimplexBoundary
  have hGsub : G ⊆ Δ := by
    rw [hGΔ]
    exact (image_mono (fun _ hx => hx.1)).trans hr.image_eq.subset
  have hsep := not_isPreconnected_sdiff_of_disjoint_disk_and_carrier hS hG hGS ⟨r, hr⟩
    hGsub hΔZ hZ hZS hZgen htriv
  exact hS.isPLTorus_frontier.exists_isPLHomeomorphOn_disk_of_not_isPreconnected_sdiff hG hGS hsep

end DifferentialGeometry.Topology.PiecewiseLinear.TorusLinking
