/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Combinatorics.HeightConnectivity
import DifferentialGeometry.Topology.PiecewiseLinear.HeightSubcomplex
import DifferentialGeometry.Topology.PiecewiseLinear.LinkHeightConnected
import DifferentialGeometry.Topology.SimplicialComplex.EdgeConnectivity

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem isPreconnected_inter_affine_lt_of_edgeGraph_preconnected
    (K : Geometry.SimplicialComplex ℝ E) (a : E →ᵃ[ℝ] ℝ) (r : ℝ)
    (hG : ((SimplicialComplex.edgeGraph K).induce {v : K.vertices | a v < r}).Preconnected) :
    IsPreconnected (K.space ∩ {x | a x < r}) := by
  classical
  let V := {v : K.vertices | a v < r}
  let C := fun v : V => closedStar K (v : K.vertices) ∩ {x | a x < r}
  have hcover : K.space ∩ {x | a x < r} = ⋃ v : V, C v := by
    apply Subset.antisymm
    · rintro x ⟨hxK, hxr⟩
      obtain ⟨s, hs, hxs⟩ := K.mem_space_iff.mp hxK
      obtain ⟨v, hv, hvr⟩ : ∃ v ∈ s, a v < r := by
        by_contra h
        push Not at h
        have hsub : convexHull ℝ (s : Set E) ⊆ {y | r ≤ a y} :=
          convexHull_min h ((convex_Ici r).affine_preimage a)
        exact not_lt_of_ge (show r ≤ a x from hsub hxs) (show a x < r from hxr)
      have hvK : v ∈ K.vertices :=
        K.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
      exact mem_iUnion.mpr ⟨⟨⟨v, hvK⟩, hvr⟩,
        mem_biUnion ⟨hs, subset_convexHull ℝ _ hv⟩ hxs, hxr⟩
    · intro x hx
      obtain ⟨v, hxv, hxr⟩ := mem_iUnion.mp hx
      exact ⟨closedStar_subset_space K _ hxv, hxr⟩
  rw [hcover]
  apply IsPreconnected.iUnion_of_reflTransGen
  · intro v
    exact (((starConvex_closedStar K).inter
      (((convex_Iio r).affine_preimage a).starConvex v.2)).isPathConnected
      ⟨mem_closedStar_of_singleton_mem K v.1.2, v.2⟩).isConnected.isPreconnected
  · intro u v
    have hadj {b c : V}
        (hbc : ((SimplicialComplex.edgeGraph K).induce V).Adj b c) : (C b ∩ C c).Nonempty := by
      refine ⟨b.1, ⟨mem_closedStar_of_singleton_mem K b.1.2, b.2⟩, ?_, b.2⟩
      exact mem_biUnion
        ⟨hbc.2, subset_convexHull ℝ (({(b.1 : E), (c.1 : E)} : Finset E) : Set E) (by simp)⟩
        (subset_convexHull ℝ (({(b.1 : E), (c.1 : E)} : Finset E) : Set E) (by simp))
    apply Relation.ReflTransGen.mono (fun _ _ h => hadj h)
    exact (((SimplicialComplex.edgeGraph K).induce V).reachable_iff_reflTransGen u v).mp (hG u v)

theorem isPreconnected_inter_affine_lt_of_preconnected_lower_links [FiniteDimensional ℝ E]
    [DecidableEq E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsPreconnected K.space) (a : E →ᵃ[ℝ] ℝ) (hinj : InjOn a K.vertices)
    (hlinks : ∀ p ∈ K.vertices,
      IsPreconnected ((SimplicialComplex.geometricLink K {p}).space ∩ {x | a x < a p})) (r : ℝ) :
    IsPreconnected (K.space ∩ {x | a x < r}) := by
  classical
  let G := SimplicialComplex.edgeGraph K
  let _ : Finite K.vertices := (SimplicialComplex.finite_vertices K).to_subtype
  have hG : G.Preconnected := edgeGraph_preconnected_of_isPreconnected_space K hK
  have hf : Function.Injective (fun v : K.vertices => a v) :=
    fun u v huv => Subtype.ext (hinj u.2 v.2 huv)
  apply isPreconnected_inter_affine_lt_of_edgeGraph_preconnected K a r
  apply Combinatorics.preconnected_induce_lt_of_lower_neighbors_reachable G hG _ hf
  intro p u v hpu hpv
  let L := restrict (SimplicialComplex.geometricLink K {p.val}) {x | a x < a p}
  let _ : Finite L.faces := (restrict_faces_finite _ _).to_subtype
  have hL : (SimplicialComplex.edgeGraph L).Preconnected :=
    edgeGraph_preconnected_of_isPreconnected_space L
      (isPreconnected_restrict_affine_lt_of_isPreconnected _ a (a p) (hlinks p p.2))
  have hmem (w : {x : K.vertices | a x < a p}) (hpw : G.Adj p w) : (w.1 : E) ∈ L.vertices := by
    apply (mem_restrict_affine_lt_vertices_iff _ a (a p)).mpr
    refine ⟨?_, w.2⟩
    apply (SimplicialComplex.mem_geometricLink_singleton K p {w.1.val}).mpr
    refine ⟨Finset.singleton_nonempty _, ?_, ?_⟩
    · simpa only [Finset.mem_singleton] using fun h => hpw.1 (Subtype.ext h)
    · convert hpw.2 using 1
      ext z
      simp only [Finset.mem_insert, Finset.mem_singleton]
  let φ : SimplicialComplex.edgeGraph L →g G.induce {x : K.vertices | a x < a p} := {
    toFun x :=
      let hx := (mem_restrict_affine_lt_vertices_iff _ a (a p)).mp x.2
      ⟨⟨x, SimplicialComplex.geometricLink_le K {p.val} hx.1⟩, hx.2⟩
    map_rel' := by
      intro x y hxy
      refine ⟨?_, SimplicialComplex.geometricLink_le K {p.val} hxy.2.1⟩
      intro heq
      apply hxy.1
      apply Subtype.ext
      exact congrArg (fun z : K.vertices => (z : E)) heq
  }
  exact (hL ⟨u.1, hmem u hpu⟩ ⟨v.1, hmem v hpv⟩).map φ

theorem isPreconnected_halfSpaces_of_heightIndex_eq_zero [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsPLSphere 2 K.space) (hdimE : Module.finrank ℝ E = 3)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices)
    (hzero : heightIndex K.space ℓ = 0) (r : ℝ) :
    IsPreconnected (K.space ∩ {x | ℓ x < r}) ∧
      IsPreconnected (K.space ∩ {x | r < ℓ x}) := by
  classical
  have hlinks (p : E) (hp : p ∈ K.vertices) :=
    isPreconnected_geometricLink_halfSpaces_of_heightIndex_eq_zero K hK hdimE ℓ hℓ hinj hzero hp
  refine ⟨isPreconnected_inter_affine_lt_of_preconnected_lower_links K hK.isConnected.isPreconnected
    ℓ.toLinearMap.toAffineMap hinj (fun p hp => (hlinks p hp).1) r, ?_⟩
  have hinj' : InjOn (-ℓ) K.vertices := by
    intro x hx y hy hxy
    exact hinj hx hy (neg_injective hxy)
  have hlinks' : ∀ p ∈ K.vertices,
      IsPreconnected ((SimplicialComplex.geometricLink K {p}).space ∩ {x | (-ℓ) x < (-ℓ) p}) := by
    intro p hp
    simpa only [neg_apply, neg_lt_neg_iff] using (hlinks p hp).2
  have h := isPreconnected_inter_affine_lt_of_preconnected_lower_links K
      hK.isConnected.isPreconnected
    (-ℓ).toLinearMap.toAffineMap hinj' hlinks' (-r)
  change IsPreconnected (K.space ∩ {x | -ℓ x < -r}) at h
  simpa only [neg_lt_neg_iff] using h

end DifferentialGeometry.Topology.PiecewiseLinear
