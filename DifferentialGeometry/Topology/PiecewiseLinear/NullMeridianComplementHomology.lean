/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Homology.Algebra.PrimitiveSummand
import DifferentialGeometry.Topology.PiecewiseLinear.CollaredHomologyGeneration
import DifferentialGeometry.Topology.PiecewiseLinear.NonseparatingPolygonHomologySummand
import DifferentialGeometry.Topology.PiecewiseLinear.SolidTorusBoundaryDeletionHomology
import DifferentialGeometry.Topology.PiecewiseLinear.SolidTorusInteriorHomology
import Mathlib.Geometry.Manifold.Instances.Sphere

open Set Topology
open scoped ContinuousMap

namespace DifferentialGeometry.Topology.PiecewiseLinear.TorusLinking

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private def complementPreimageHomeomorph (P G : Set E3) :
    (((↑) : (Gᶜ : Set E3) → E3) ⁻¹' P) ≃ₜ ↥(P \ G) where
  toFun x := ⟨x.1.1, x.2, x.1.2⟩
  invFun x := ⟨⟨x.1, x.2.2⟩, x.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

private theorem pathConnectedSpace_frontier_complement {T G : Set E3}
    (hT : IsPLTorus T) (hG : IsPLSphere 1 G) (hGT : G ⊆ T)
    (hnonsep : IsPreconnected (T \ G)) :
    PathConnectedSpace (((↑) : T → E3) ⁻¹' Gᶜ) := by
  obtain ⟨e⟩ := hT.2
  let _ : LocallyPathConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 1)) _
  let _ : LocallyPathConnectedSpace T := e.isOpenEmbedding.locallyPathConnectedSpace
  have ho : IsOpen (((↑) : T → E3) ⁻¹' Gᶜ) :=
    hG.isPolyhedron.isClosed.isOpen_compl.preimage continuous_subtype_val
  let _ := ho.locallyPathConnectedSpace
  have hp : IsPreconnected (((↑) : T → E3) ⁻¹' Gᶜ) := by
    apply IsInducing.subtypeVal.isPreconnected_image.mp
    rw [Subtype.image_preimage_coe]
    exact hnonsep
  have hn : (((↑) : T → E3) ⁻¹' Gᶜ).Nonempty := by
    obtain ⟨j, _⟩ := hT.exists_homotopic_inclusion_in_complement hG hGT hnonsep
    obtain ⟨x, hx⟩ := hG.isPathConnected_one.nonempty
    exact ⟨⟨j ⟨x, hx⟩, (j ⟨x, hx⟩).2.1⟩, (j ⟨x, hx⟩).2.2⟩
  let _ : ConnectedSpace (((↑) : T → E3) ⁻¹' Gᶜ) :=
    isConnected_iff_connectedSpace.mp ⟨hn, hp⟩
  exact PathConnectedSpace.of_locallyPathConnectedSpace

private noncomputable def firstHomologyInclusion {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) :
    integralSingularHomology 1 A →ₗ[ℤ] integralSingularHomology 1 B :=
  integralSingularHomologyMap 1 ⟨inclusion hAB, continuous_inclusion hAB⟩

private theorem firstHomologyInclusion_comp {X : Type*} [TopologicalSpace X]
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

private theorem nonempty_solidTorus_homology_equiv_int {S : Set E3}
    (hS : IsTopologicalSolidTorus S) : Nonempty (integralSingularHomology 1 S ≃+ ℤ) := by
  obtain ⟨φ⟩ := hS
  let D := Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1
  let C := Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1
  let p : D := ⟨0, by simp [D]⟩
  let e : S ≃ₕ C := φ.toHomotopyEquiv.trans
    ((Homeomorph.prodComm D C).toHomotopyEquiv.trans
      (DifferentialGeometry.HomotopyEquiv.productConvex C (convex_closedBall _ _) p))
  exact ⟨((integralSingularHomologyHomotopyEquiv 1 e).trans
    (integralSphereTopHomologyEquiv 0 (EuclideanSpace ℝ (Fin 2)) (by simp))).toAddEquiv⟩

private theorem firstHomologyInclusion_eq_zero_of_null_piOne {S G : Set E3}
    (hG : IsPLSphere 1 G) (hGS : G ⊆ S)
    (htriv : ∀ (x : G) (g : FundamentalGroup G x),
      FundamentalGroup.map (⟨inclusion hGS, continuous_inclusion hGS⟩ : C(G, S)) x g = 1)
    (a : integralSingularHomology 1 G) : firstHomologyInclusion hGS a = 0 := by
  let _ : PathConnectedSpace G := isPathConnected_iff_pathConnectedSpace.mp hG.isPathConnected_one
  obtain ⟨x⟩ : Nonempty G := inferInstance
  obtain ⟨g, hg⟩ := hurewiczOne_surjective x (Multiplicative.ofAdd a)
  have ha : (hurewiczOne x g).toAdd = a := congrArg Multiplicative.toAdd hg
  rw [← ha]
  change integralSingularHomologyMap 1
    (⟨inclusion hGS, continuous_inclusion hGS⟩ : C(G, S)) (hurewiczOne x g).toAdd = 0
  rw [← hurewiczOne_map, htriv, map_one]
  rfl

private theorem surjective_meridian_of_homology_data {S G E : Set E3}
    (hS : IsCombinatorialSolidTorus S) (hG : IsPLSphere 1 G)
    (hGT : G ⊆ frontier S) (hTS : frontier S ⊆ S) (hTE : frontier S ⊆ E)
    (hIG : interior S ⊆ Gᶜ) (hnonsep : IsPreconnected (frontier S \ G))
    (htriv : ∀ (hsub : G ⊆ S) (x : G) (g : FundamentalGroup G x),
      FundamentalGroup.map (⟨inclusion hsub, continuous_inclusion hsub⟩ : C(G, S)) x g = 1)
    (hambient : Function.Bijective (fun a : integralSingularHomology 1 (frontier S) =>
      (firstHomologyInclusion hTS a, firstHomologyInclusion hTE a)))
    (hdelS : Function.Bijective
      (firstHomologyInclusion (sdiff_subset : S \ G ⊆ S)))
    (hdelE : Function.Bijective
      (firstHomologyInclusion (sdiff_subset : E \ G ⊆ E)))
    (hjoint : ∀ a : integralSingularHomology 1 (Gᶜ : Set E3),
      ∃ p : integralSingularHomology 1 (S \ G : Set E3),
      ∃ q : integralSingularHomology 1 (E \ G : Set E3),
        firstHomologyInclusion (fun _ hx => hx.2) p +
          firstHomologyInclusion (fun _ hx => hx.2) q = a)
    (hInt : Function.Surjective
      (firstHomologyInclusion (interior_subset : interior S ⊆ S))) :
    Function.Surjective (firstHomologyInclusion hIG) := by
  obtain ⟨eP, heP⟩ := hS.isPLTorus_frontier.exists_firstHomology_equiv_prod_of_nonseparating
    hG hGT hnonsep
  obtain ⟨eS⟩ := nonempty_solidTorus_homology_equiv_int hS.1
  let m := (firstHomologyInclusion hTS).prod (firstHomologyInclusion hTE)
  let eM := AddEquiv.ofBijective m.toAddMonoidHom hambient
  let e := (eP.symm.toAddEquiv.trans eM).trans
    (eS.prodCongr (AddEquiv.refl (integralSingularHomology 1 E)))
  have he (a : integralSingularHomology 1 G) :
      e (a, 0) = (0, firstHomologyInclusion (hGT.trans hTE) a) := by
    have hpinv : eP.symm (a, 0) = firstHomologyInclusion hGT a := by
      apply eP.injective
      rw [eP.apply_symm_apply]
      exact (heP a).symm
    change (eS (firstHomologyInclusion hTS (eP.symm (a, 0))),
      firstHomologyInclusion hTE (eP.symm (a, 0))) = _
    rw [hpinv, firstHomologyInclusion_comp, firstHomologyInclusion_comp,
      firstHomologyInclusion_eq_zero_of_null_piOne hG _ (htriv _), map_zero]
  have hGE : Function.Surjective (firstHomologyInclusion (hGT.trans hTE)) := by
    intro b
    obtain ⟨a, ha⟩ := DifferentialGeometry.surjective_snd_of_equiv_prod_fst_eq_zero
      e (fun a => congrArg Prod.fst (he a)) b
    exact ⟨a, (congrArg Prod.snd (he a)).symm.trans ha⟩
  obtain ⟨j, hj⟩ := hS.isPLTorus_frontier.exists_homotopic_inclusion_in_complement hG hGT hnonsep
  have hTGS : frontier S \ G ⊆ S \ G := fun _ hx => ⟨hTS hx.1, hx.2⟩
  have hTGE : frontier S \ G ⊆ E \ G := fun _ hx => ⟨hTE hx.1, hx.2⟩
  let jS : C(G, ↥(S \ G)) :=
    (⟨inclusion hTGS, continuous_inclusion hTGS⟩ : C(↥(frontier S \ G), ↥(S \ G))).comp j
  let jE : C(G, ↥(E \ G)) :=
    (⟨inclusion hTGE, continuous_inclusion hTGE⟩ : C(↥(frontier S \ G), ↥(E \ G))).comp j
  have hjS (a : integralSingularHomology 1 G) :
      firstHomologyInclusion sdiff_subset (integralSingularHomologyMap 1 jS a) = 0 := by
    have h := integralSingularHomologyMap_homotopic 1
      ((ContinuousMap.Homotopic.refl
        (⟨inclusion hTS, continuous_inclusion hTS⟩ : C(frontier S, S))).comp hj)
    change integralSingularHomologyMap 1 _ (integralSingularHomologyMap 1 jS a) = 0
    rw [← LinearMap.comp_apply, ← integralSingularHomologyMap_comp]
    exact (LinearMap.congr_fun h a).trans
      (firstHomologyInclusion_eq_zero_of_null_piOne hG (hGT.trans hTS)
        (htriv (hGT.trans hTS)) a)
  have hjE (a : integralSingularHomology 1 G) :
      firstHomologyInclusion sdiff_subset (integralSingularHomologyMap 1 jE a) =
        firstHomologyInclusion (hGT.trans hTE) a := by
    have h := integralSingularHomologyMap_homotopic 1
      ((ContinuousMap.Homotopic.refl
        (⟨inclusion hTE, continuous_inclusion hTE⟩ : C(frontier S, E))).comp hj)
    change integralSingularHomologyMap 1 _ (integralSingularHomologyMap 1 jE a) = _
    rw [← LinearMap.comp_apply, ← integralSingularHomologyMap_comp]
    exact LinearMap.congr_fun h a
  have hzero (q : integralSingularHomology 1 (E \ G : Set E3)) :
      firstHomologyInclusion (show E \ G ⊆ Gᶜ from fun _ hx => hx.2) q = 0 := by
    obtain ⟨a, ha⟩ := hGE (firstHomologyInclusion sdiff_subset q)
    have hqa : integralSingularHomologyMap 1 jE a = q := hdelE.1 ((hjE a).trans ha)
    have hsa : integralSingularHomologyMap 1 jS a = 0 :=
      hdelS.1 ((hjS a).trans (map_zero _).symm)
    rw [← hqa]
    have hmaps :
        (⟨inclusion (show E \ G ⊆ Gᶜ from fun _ hx => hx.2),
          continuous_inclusion _⟩ : C(↥(E \ G), ↥(Gᶜ))).comp jE =
        (⟨inclusion (show S \ G ⊆ Gᶜ from fun _ hx => hx.2),
          continuous_inclusion _⟩ : C(↥(S \ G), ↥(Gᶜ))).comp jS := by ext x; rfl
    change integralSingularHomologyMap 1 _ (integralSingularHomologyMap 1 jE a) = 0
    rw [← LinearMap.comp_apply, ← integralSingularHomologyMap_comp, hmaps,
      integralSingularHomologyMap_comp, LinearMap.comp_apply, hsa, map_zero]
  intro a
  obtain ⟨p, q, hpq⟩ := hjoint a
  rw [hzero, add_zero] at hpq
  obtain ⟨i, hi⟩ := hInt (firstHomologyInclusion sdiff_subset p)
  have hIP : interior S ⊆ S \ G := fun x hx => ⟨interior_subset hx, hIG hx⟩
  have hip : firstHomologyInclusion hIP i = p := by
    apply hdelS.1
    rw [firstHomologyInclusion_comp]
    exact hi
  refine ⟨i, ?_⟩
  calc
    firstHomologyInclusion hIG i =
        firstHomologyInclusion (show S \ G ⊆ Gᶜ from fun _ hx => hx.2)
          (firstHomologyInclusion hIP i) := (firstHomologyInclusion_comp _ _ _).symm
    _ = a := by rw [hip]; exact hpq

theorem surjective_firstHomologyInclusion_of_nullhomotopic_meridian
    {S G : Set (EuclideanSpace ℝ (Fin 3))}
    (hS : IsCombinatorialSolidTorus S) (hG : IsPLSphere 1 G)
    (hGS : G ⊆ frontier S) (hIG : interior S ⊆ Gᶜ)
    (hnonsep : IsPreconnected (frontier S \ G))
    (htriv : ∀ (hsub : G ⊆ S) (x : G) (g : FundamentalGroup G x),
      FundamentalGroup.map (⟨Set.inclusion hsub, continuous_inclusion hsub⟩ : C(G, S)) x g = 1) :
    Function.Surjective (firstHomologyInclusion hIG) := by
  have hTS : frontier S ⊆ S := hS.isPolyhedron.isClosed.frontier_subset
  have hTE : frontier S ⊆ (interior S)ᶜ := fun _ hx => hx.2
  apply surjective_meridian_of_homology_data hS hG hGS hTS hTE hIG hnonsep htriv
  · exact hS.bijective_integralSingularHomologyMap_frontier_pair
  · exact hS.bijective_integralSingularHomologyMap_of_interior_subset (A := S \ G) 1
      (fun _ hx => ⟨interior_subset hx, hIG hx⟩) sdiff_subset
  · exact hS.bijective_integralSingularHomologyMap_of_exterior_subset
      (A := (interior S)ᶜ \ G) 1
      (fun _ hx => ⟨fun hi => hx (interior_subset hi), fun hg => hx (hTS (hGS hg))⟩)
      sdiff_subset
  · intro a
    obtain ⟨c, hcover, hmeet, hScl, hEcl, _, _⟩ := hS.exists_collared_exterior_cover
    let _ := pathConnectedSpace_frontier_complement hS.isPLTorus_frontier hG hGS hnonsep
    have hGr : G ⊆ Set.range (Subtype.val : frontier S → E3) := by
      simpa only [Subtype.range_coe] using hGS
    have hmeet' : S ∩ (interior S)ᶜ = Set.range (Subtype.val : frontier S → E3) := by
      simpa only [Subtype.range_coe] using hmeet
    obtain ⟨p, q, hpq⟩ := c.exists_integralFirstHomology_sum_of_deleted_collared_cover
      hG.isPolyhedron.isClosed hGr hcover hmeet' hScl hEcl a
    let eP := complementPreimageHomeomorph S G
    let eQ := complementPreimageHomeomorph (interior S)ᶜ G
    refine ⟨integralSingularHomologyMap 1 (eP : C(_, _)) p,
      integralSingularHomologyMap 1 (eQ : C(_, _)) q, ?_⟩
    change integralSingularHomologyMap 1 _ (integralSingularHomologyMap 1 _ p) +
      integralSingularHomologyMap 1 _ (integralSingularHomologyMap 1 _ q) = a
    rw [← LinearMap.comp_apply, ← integralSingularHomologyMap_comp,
      ← LinearMap.comp_apply, ← integralSingularHomologyMap_comp]
    exact hpq
  · exact (hS.bijective_integralSingularHomologyMap_of_interior_subset 1
      subset_rfl interior_subset).2

end DifferentialGeometry.Topology.PiecewiseLinear.TorusLinking
