/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.AnnularChainRimTubePrism
import DifferentialGeometry.Topology.PiecewiseLinear.AnnularChainRimGenerators
import DifferentialGeometry.Topology.PiecewiseLinear.AnnularChainRimRetraction
import DifferentialGeometry.Topology.PiecewiseLinear.AnnularChainRimTransfer
import DifferentialGeometry.Topology.PiecewiseLinear.AnnularChainRimTails
import DifferentialGeometry.Topology.PiecewiseLinear.IsTopologicalSphereImageSplitRim
import DifferentialGeometry.Topology.PiecewiseLinear.NonseparatingPolygonCarrier

open Set Topology
open scoped ContinuousMap
open DifferentialGeometry.Simplex

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "CircleModel" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1

variable {φ : E3 → E3} {Pt : ℤ → E3}
  {Dp Dpint J A S T S'' T'' H B Jlo Jhi : ℤ → Set E3}
  {Dimg Dbdimg W I : Set E3} {P' : E3}

private theorem rim_subset_closure_of_prism
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (hch : IsAnnularChain H B Jlo Jhi (fun i => φ '' S i) S'' T'' P')
    (hcompact : IsCompact (closure I)) {Q : Set E3} (hIQ : I ⊆ Q)
    (e : (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) × Icc (-1 : ℝ) 1) ≃ₜ Q)
    (hD : range (fun p => (e (p, ⟨0, by norm_num⟩) : E3)) = Dimg)
    (hR : range (fun b : boundary (Fin 3) => (e (b.val, ⟨0, by norm_num⟩) : E3)) = Dbdimg)
    (hP : (e (Convexity.StdSimplex.coordinateBarycenter, ⟨0, by norm_num⟩) : E3) = P')
    (eR : Dbdimg ≃ₜ CircleModel) : Dbdimg ⊆ closure (annularChain H B P') := by
  classical
  obtain ⟨U, r, hU, hrim, d, hd, s, hs⟩ := exists_prism_rim_retraction e hD hR hP
  obtain ⟨c, hc⟩ := htw.exists_annuli_cylinder_homeomorph
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 2)) := by
    rw [← Module.finrank_eq_rank', finrank_euclideanSpace_fin]
    norm_num
  have hcircle := isPathConnected_sphere hrank (0 : EuclideanSpace ℝ (Fin 2)) zero_le_one
  have : PathConnectedSpace CircleModel := isPathConnected_iff_pathConnectedSpace.mp hcircle
  have : PathConnectedSpace ↥(Dimg \ (Dbdimg ∪ {P'})) :=
    c.surjective.pathConnectedSpace c.continuous
  have hrd (x : ↥(Dimg \ (Dbdimg ∪ {P'}))) :
      Function.Surjective (FundamentalGroup.map (r.comp d) x) :=
    surjective_fundamentalGroup_map_of_continuous_section (r.comp d) s hs x
  intro x hx
  rw [mem_closure_iff]
  intro O hO hxO
  let xr : Dbdimg := ⟨x, hx⟩
  let V : Set U := r ⁻¹' {xr}ᶜ ∪
    (fun y : U => ((y : Q) : E3)) ⁻¹' O
  have hV : IsOpen V := (isOpen_compl_singleton.preimage r.continuous).union
    (hO.preimage (continuous_subtype_val.comp continuous_subtype_val))
  have hUV : IsOpen ((Subtype.val : U → Q) '' V) := hU.isOpenMap_subtype_val V hV
  obtain ⟨V₀, hV₀, hV₀eq⟩ := isOpen_induced_iff.mp hUV
  have hRV₀ : Dbdimg ⊆ V₀ := by
    intro z hz
    obtain ⟨y, hy, hry⟩ := hrim ⟨z, hz⟩
    have hyV : y ∈ V := by
      by_cases hzx : z = x
      · right
        change ((y : Q) : E3) ∈ O
        change ((y : Q) : E3) = z at hy
        rw [hy, hzx]
        exact hxO
      · left
        change r y ≠ xr
        rw [hry]
        exact fun h => hzx (congrArg Subtype.val h)
    have hyV₀ : (y : Q) ∈ (Subtype.val : Q → E3) ⁻¹' V₀ :=
      hV₀eq.symm.subset ⟨y, hyV, rfl⟩
    change ((y : Q) : E3) = z at hy
    change ((y : Q) : E3) ∈ V₀ at hyV₀
    simpa only [hy] using hyV₀
  obtain ⟨m, hm⟩ := htw.exists_upper_tail_subset hcompact hV₀ hRV₀
  let j : ℤ := max m 0
  have hmj : m ≤ 2 * j := by dsimp [j]; omega
  have hSQ : φ '' S (2 * j) ⊆ Q := (htw.subsetInterior _).trans hIQ
  have hSV : ∀ y : φ '' S (2 * j), (⟨y.val, hSQ y.property⟩ : Q) ∈
      (Subtype.val : U → Q) '' V := by
    intro y
    apply hV₀eq.subset
    exact hm (2 * j) hmj y.property
  have hinner : S'' (2 * j) ⊆ φ '' S (2 * j) := by
    simpa using ((htw.config (2 * j)).innerSubset (0 : Fin 3)).trans interior_subset
  have hinnerQ : S'' (2 * j) ⊆ Q := hinner.trans hSQ
  have hinnerU (y : S'' (2 * j)) : (⟨y.val, hinnerQ y.property⟩ : Q) ∈ U := by
    obtain ⟨z, -, hz⟩ := hSV ⟨y.val, hinner y.property⟩
    exact hz ▸ z.property
  let q : C(S'' (2 * j), U) :=
    ⟨fun y => ⟨⟨y.val, hinnerQ y.property⟩, hinnerU y⟩,
      (continuous_subtype_val.subtype_mk _).subtype_mk _⟩
  have hJinner : φ '' J (2 * j) ⊆ S'' (2 * j) := by
    simpa using (htw.config (2 * j)).image_circle_subset (0 : Fin 3) (0 : Fin 4) (Or.inl rfl)
  let a : C(φ '' J (2 * j), S'' (2 * j)) :=
    ⟨Set.inclusion hJinner, continuous_inclusion hJinner⟩
  let aD : C(φ '' J (2 * j), ↥(Dimg \ (Dbdimg ∪ {P'}))) :=
    ⟨Set.inclusion (htw.circle_image_subset_punctured_disk (2 * j)),
      continuous_inclusion _⟩
  have hqa : q.comp a = d.comp aD := by
    apply ContinuousMap.ext
    intro z
    apply Subtype.ext
    apply Subtype.ext
    exact (hd (aD z)).symm
  obtain ⟨z₀, hz₀⟩ := hcircle.nonempty
  have hcJ : (c (⟨z₀, hz₀⟩, (2 * j : ℤ))) ∈
      (Subtype.val : ↥(Dimg \ (Dbdimg ∪ {P'})) → E3) ⁻¹' (φ '' J (2 * j)) := by
    change (c (⟨z₀, hz₀⟩, (2 * j : ℤ)) : E3) ∈ φ '' J (2 * j)
    rw [← hc (2 * j)]
    exact mem_range_self _
  let z : φ '' J (2 * j) := ⟨c (⟨z₀, hz₀⟩, (2 * j : ℤ)), hcJ⟩
  have hfa : Function.Surjective (FundamentalGroup.map ((r.comp q).comp a) z) := by
    have heq : (r.comp q).comp a = (r.comp d).comp aD := by
      rw [ContinuousMap.comp_assoc, hqa, ← ContinuousMap.comp_assoc]
    rw [heq, fundamentalGroup_map_continuousMap_comp, MonoidHom.coe_comp]
    exact (hrd (aD z)).comp (htw.circle_fundamentalGroup_bijective (2 * j) _ z).2
  have htorus : IsTopologicalSolidTorus (S'' (2 * j)) := by
    simpa using ((htw.config (2 * j)).isPolyhedralSolidTorus (0 : Fin 3)).1
  have : PathConnectedSpace (S'' (2 * j)) :=
    isPathConnected_iff_pathConnectedSpace.mp htorus.isPathConnected
  have : CompactSpace (S'' (2 * j)) := (Classical.choice htorus).symm.compactSpace
  have hclosed : IsClosed (S'' (2 * j)) :=
    (isCompact_iff_compactSpace.mpr inferInstance).isClosed
  have hlo : Jlo j ⊆ S'' (2 * j) := by
    have hbd : T'' (2 * j) = frontier (S'' (2 * j)) := by
      simpa using (htw.config (2 * j)).boundaryEq (0 : Fin 3)
    exact (hch.loSubset j).trans (hbd ▸ hclosed.frontier_subset)
  let g : C(Jlo j, S'' (2 * j)) := ⟨Set.inclusion hlo, continuous_inclusion hlo⟩
  obtain ⟨eH, -, heH⟩ := (hch.half j).exists_homeomorph
  let b₀ : stdSimplexBoundary 2 :=
    ⟨Pi.single (0 : Fin 3) 1, Convexity.StdSimplex.single_mem_coordinateSet ℝ 0, ⟨1, by simp⟩⟩
  let y₀ : Jlo j := ⟨eH (b₀, 1), heH ▸ mem_range_self b₀⟩
  have hfg := surjective_fundamentalGroup_map_comp_of_surjective_comp a g (r.comp q) z y₀
    hfa (hch.loGenerator j hlo y₀)
  have honto := surjective_of_fundamentalGroup_map_surjective_to_homeomorphic_circle
    eR ((r.comp q).comp g) y₀ hfg
  obtain ⟨y, hy⟩ := honto xr
  obtain ⟨w, hw, hwy⟩ := hSV ⟨y.val, hinner (hlo y.property)⟩
  have hwq : w = q (g y) := by
    apply Subtype.ext
    exact hwy
  have hyO : (y : E3) ∈ O := by
    rcases hw with hw | hw
    · change r w ≠ xr at hw
      exact False.elim (hw (hwq ▸ hy))
    · exact congrArg Subtype.val hwy ▸ hw
  have hychain : (y : E3) ∈ annularChain H B P' := by
    left
    apply mem_iUnion.mpr
    refine ⟨j, Or.inl ?_⟩
    exact ((hch.halfInterBridge j).symm.subset y.property).1
  exact ⟨y, hyO, hychain⟩

theorem IsTube.splitRim_subset_closure_annularChain
    {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3}
    {C : E3 → Set E3} {D Dbd : Finset E3 → Set E3} {h : E3 → E3} {u v : E3}
    (ht : IsTube K N C D Dbd h N') (hu : u ∈ K.vertices)
    (hv : v ∈ K.vertices) (huv : u ≠ v)
    (he : ({u, v} : Finset E3) ∈ K.faces)
    (hP' : P' = h (({u, v} : Finset E3).centroid ℝ id))
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T''
      (h '' D {u, v}) (h '' Dbd {u, v}) W (interior (h '' C u ∪ h '' C v)) P')
    (hch : IsAnnularChain H B Jlo Jhi (fun i => φ '' S i) S'' T'' P') :
    h '' Dbd {u, v} ⊆ closure (annularChain H B P') := by
  obtain ⟨e, hD, hR, hP⟩ := ht.exists_centered_product_homeomorph hu hv huv he
  obtain ⟨eR⟩ := isTopologicalSphere_image_splitRim ht he (Finset.card_pair huv)
  exact rim_subset_closure_of_prism htw hch (ht.isCompact_closure_interior_pair hu hv)
    interior_subset e hD hR (hP.trans hP'.symm) eR

end DifferentialGeometry.Topology.PiecewiseLinear
