/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexCollapse
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.SingularCell

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem NormalSystem.exists_source_collapse
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (S : NormalSystem E) :
    ∃ S' : NormalSystem E,
      S'.ambientComplex = S.ambientComplex ∧ S'.imageComplex = S.imageComplex ∧
      S'.loopComplex = S.loopComplex ∧ S'.manifoldComplex = S.manifoldComplex ∧
      S'.boundaryComplex = S.boundaryComplex ∧ S'.boundaryNeighborhood = S.boundaryNeighborhood ∧
      IsSubdivision S'.sourceComplex S.sourceComplex ∧
      S'.sourceComplex.space = S.sourceComplex.space ∧
      {v ∈ S'.sourceComplex.faces | v.card = 3}.ncard =
        {v ∈ S.sourceComplex.faces | v.card = 3}.ncard + 6 ∧
      EqOn S'.singularMap S.singularMap (frontier S.sourceComplex.space) ∧
      (∀ θ, (S'.boundaryParam θ : EuclideanSpace ℝ (Fin 2)) = S.boundaryParam θ) ∧
      HEq S'.basepoint S.basepoint ∧ HEq S'.boundaryLoop S.boundaryLoop ∧
      HEq S'.connector S.connector ∧ HEq S'.normalSubgroup S.normalSubgroup ∧
      HEq S'.loopConjugacyClass S.loopConjugacyClass ∧
      ∃ y : E, (S'.sourceComplex.space ∩ S'.singularMap ⁻¹' {y}).Infinite ∧
        (¬∀ x ∈ S'.sourceComplex.space,
          ∃ U ∈ 𝓝[S'.sourceComplex.space] x, InjOn S'.singularMap U) ∧
        ∃ u ∈ S'.sourceComplex.faces, u.card = 3 ∧
          convexHull ℝ (u : Set (EuclideanSpace ℝ (Fin 2))) ⊆
            interior S'.sourceComplex.space ∧
          EqOn S'.singularMap (fun _ => y) (convexHull ℝ (u : Set (EuclideanSpace ℝ (Fin 2)))) := by
  classical
  let _ : DecidableEq (EuclideanSpace ℝ (Fin 2)) := Classical.decEq _
  let _ : Finite S.sourceComplex.faces := S.finite_source.to_subtype
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := by simp
  obtain ⟨x, hx⟩ := S.source_isPLBall.nonempty
  obtain ⟨s, hs, -⟩ := S.sourceComplex.mem_space_iff.mp hx
  obtain ⟨t, ht, -, htc⟩ :=
    S.source_isPLBall.isCombinatorialManifoldWithBoundary.exists_face_superset_card_eq hs
  obtain ⟨a, b, c, hab, hac, hbc, htabc⟩ := Finset.card_eq_three.mp htc
  obtain ⟨R, q, u, hR, hfin, hcount, hvertices, hmap, hsurj, hpres, -, -, -,
    hu, huc, hinner, hconst⟩ :=
    exists_inner_triangle_collapse hdim S.sourceComplex hab hac hbc (htabc ▸ ht)
  let _ : Finite R.faces := hfin.to_subtype
  have hboundary : EqOn (simplicialMap R (S.vertexMap ∘ q)) S.singularMap
      (frontier S.sourceComplex.space) := by
    intro z hz
    have hzCostar := frontier_subset_geometricFaceCostar S.sourceComplex ht
      (by rw [hdim]; exact htc) hz
    obtain ⟨v, hv, hzv⟩ :=
      (SimplicialComplex.geometricFaceCostar S.sourceComplex t).mem_space_iff.mp hzCostar
    have hvne : v ≠ {a, b, c} := by
      intro heq
      exact hv.2 (by rw [heq, htabc])
    change simplicialMap R (S.vertexMap ∘ q) z =
      simplicialMap S.sourceComplex S.vertexMap z
    rw [simplicialMap_eq_of_mem R _ (hpres v hv.1 hvne) hzv,
      simplicialMap_eq_of_mem S.sourceComplex _ hv.1 hzv]
    apply Finset.sum_congr rfl
    intro w hw
    have hwK : w ∈ S.sourceComplex.vertices := S.sourceComplex.down_closed hv.1
      (Finset.singleton_subset_iff.mpr hw) (Finset.singleton_nonempty w)
    have hqw : q w = w := hvertices hwK
    simp only [Function.comp_apply, hqw]
  let S' : NormalSystem E :=
    { S with
      sourceComplex := R
      finite_source := hfin
      source_isPLBall := hR.space_eq.symm ▸ S.source_isPLBall
      vertexMap := S.vertexMap ∘ q
      source_faces_map := by
        intro v hv
        rw [← Finset.image_image]
        exact S.source_faces_map _ (hmap v hv)
      image_space := S.image_space.trans
        (image_simplicialMap_eq_of_faces_image S.sourceComplex R q hmap hsurj S.vertexMap).symm
      loop_space := by
        rw [hR.space_eq, image_congr hboundary]
        exact S.loop_space
      boundaryParam := S.boundaryParam.trans
        (Homeomorph.setCongr (congrArg frontier hR.space_eq.symm))
      boundaryLoop_eq := by
        intro θ
        change (S.boundaryLoop θ : E) = simplicialMap R (S.vertexMap ∘ q) (S.boundaryParam θ)
        rw [hboundary (S.boundaryParam θ).property]
        exact S.boundaryLoop_eq θ }
  have hvertexConst {v : EuclideanSpace ℝ (Fin 2)} (hv : v ∈ u) : q v = a := by
    have hvR : v ∈ R.vertices := R.down_closed hu
      (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
    have hval := hconst (subset_convexHull ℝ _ hv)
    rwa [simplicialMap_vertex R q hvR] at hval
  have hcollapse : EqOn S'.singularMap (fun _ => S.vertexMap a)
      (convexHull ℝ (u : Set (EuclideanSpace ℝ (Fin 2)))) := by
    intro z hz
    change simplicialMap R (S.vertexMap ∘ q) z = S.vertexMap a
    rw [simplicialMap_eq_of_mem R _ hu hz]
    calc
      ∑ v ∈ u, weights u z v • (S.vertexMap ∘ q) v =
          ∑ v ∈ u, weights u z v • S.vertexMap a :=
        Finset.sum_congr rfl fun v hv => by rw [Function.comp_apply, hvertexConst hv]
      _ = S.vertexMap a := by rw [← Finset.sum_smul, sum_weights hz, one_smul]
  have hinner' : convexHull ℝ (u : Set (EuclideanSpace ℝ (Fin 2))) ⊆ interior R.space := by
    rw [hR.space_eq]
    apply hinner.trans
    rw [← htabc, ← interior_convexHull_eq_openSimplex (S.sourceComplex.indep ht)
      (by rw [hdim]; exact htc)]
    exact interior_mono (S.sourceComplex.convexHull_subset_space ht)
  have hdeg := infinite_fiber_and_not_locally_injective_of_constant_triangle hdim R hu huc hcollapse
  exact ⟨S', rfl, rfl, rfl, rfl, rfl, rfl, hR, hR.space_eq, hcount, hboundary, (fun _ => rfl),
    HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl,
    S.vertexMap a, hdeg.1, hdeg.2, u, hu, huc, hinner', hcollapse⟩

end DifferentialGeometry.Topology.PiecewiseLinear
