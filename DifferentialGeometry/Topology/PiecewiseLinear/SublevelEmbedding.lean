/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SlabEmbedding
import DifferentialGeometry.Topology.PiecewiseLinear.SublevelGluing
import DifferentialGeometry.Topology.PiecewiseLinear.HeightCone
import DifferentialGeometry.Topology.PiecewiseLinear.ConeNeighborhood
import DifferentialGeometry.Topology.HeightRange

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem isSimplyEmbedded_frontier_sublevel_of_lt_other_vertices (I : SchoenfliesInput)
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) {p : EuclideanSpace ℝ (Fin 3)} {r : ℝ}
    (hp : p ∈ K.vertices) (hpr : ℓ p < r)
    (hother : ∀ v ∈ K.vertices, v ≠ p → r < ℓ v)
    (hD : IsPLBall 2 (K.space ∩ {x | ℓ x = r})) :
    IsSimplyEmbedded (frontier (K.space ∩ ℓ ⁻¹' Iic r)) := by
  classical
  obtain ⟨L, hLfin, hspace⟩ := hD.isPolyhedron.exists_simplicialComplex
  have hL : IsConeBase p L := isConeBase_of_subset_fiber ℓ L (hspace.trans_le inter_subset_right)
      hpr.ne
  have hcone : K.space ∩ ℓ ⁻¹' Iic r = (coneComplex hL).space := by
    convert inter_le_eq_coneComplex_space_of_lt_other_vertices K ℓ.toAffineMap hp hpr hother L hL
        hspace using 1
    · ext x
      rfl
    · ext x
      simp only [mem_coneComplex_space_iff]
  rw [hcone]
  convert I.isSimplyEmbedded_frontier_coneComplex L p hL hLfin (hspace.symm ▸ hD) using 1

theorem isSimplyEmbedded_frontier_superlevel_of_other_vertices_lt (I : SchoenfliesInput)
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) {p : EuclideanSpace ℝ (Fin 3)} {r : ℝ}
    (hp : p ∈ K.vertices) (hpr : r < ℓ p)
    (hother : ∀ v ∈ K.vertices, v ≠ p → ℓ v < r)
    (hD : IsPLBall 2 (K.space ∩ {x | ℓ x = r})) :
    IsSimplyEmbedded (frontier (K.space ∩ ℓ ⁻¹' Ici r)) := by
  have hD' : IsPLBall 2 (K.space ∩ {x | (-ℓ) x = -r}) := by
    simpa only [LinearMap.neg_apply, neg_inj] using hD
  have h := isSimplyEmbedded_frontier_sublevel_of_lt_other_vertices I K (-ℓ) hp (neg_lt_neg hpr)
    (fun v hv hne => neg_lt_neg (hother v hv hne)) hD'
  have hset : (-ℓ) ⁻¹' Iic (-r) = ℓ ⁻¹' Ici r := by
    ext x
    simp only [mem_preimage, mem_Iic, mem_Ici, LinearMap.neg_apply, neg_le_neg_iff]
  rwa [hset] at h

theorem isSimplyEmbedded_frontier_sublevel_of_heightIndex_eq_zero (I : SchoenfliesInput)
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hS : IsPLSphere 2 (frontier K.space))
    (hreg : closure (interior K.space) = K.space) (hconn : IsPreconnected (interior K.space))
    (ℓ : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices)
    (hzero : heightIndex (frontier K.space) ℓ = 0) (r : ℝ)
    (hbelow : ∃ x ∈ frontier K.space, ℓ x < r) (habove : ∃ y ∈ frontier K.space, r < ℓ y) :
    IsSimplyEmbedded (frontier (K.space ∩ ℓ ⁻¹' Iic r)) := by
  classical
  have hcompact := (isPolyhedron_space K).isCompact
  let V := (SimplicialComplex.finite_vertices K).toFinset
  have hV (v : EuclideanSpace ℝ (Fin 3)) : v ∈ V ↔ v ∈ K.vertices := Set.Finite.mem_toFinset _
  have hfiber (a : ℝ) (ha : ∃ x ∈ frontier K.space, ℓ x < a)
      (hb : ∃ x ∈ frontier K.space, a < ℓ x) :
      ∃ g : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3),
        IsPLHomeomorphOn g (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (K.space ∩ {x | ℓ x = a}) ∧
        g '' stdSimplexBoundary 2 = frontier K.space ∩ {x | ℓ x = a} := by
    obtain ⟨_, _, _, _, g, hg, hgb⟩ := exists_isPLDiskDecomposition_fiber_of_heightIndex_eq_zero
      K hK hS (by simp) hreg hconn ℓ hℓ hinj hzero a ha hb
    exact ⟨g, hg, hgb⟩
  have hrec : ∀ n : ℕ, ∀ a : ℝ, (V.filter (fun v => ℓ v ≤ a)).card = n →
      (∃ x ∈ frontier K.space, ℓ x < a) → (∃ x ∈ frontier K.space, a < ℓ x) →
      IsSimplyEmbedded (frontier (K.space ∩ ℓ ⁻¹' Iic a)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro b hn hbelowB haboveB
      obtain ⟨x, hx, hxb⟩ := hbelowB
      obtain ⟨s, hs, hxs⟩ := K.mem_space_iff.mp (hcompact.isClosed.frontier_subset hx)
      obtain ⟨v, hv, hvb⟩ : ∃ v ∈ s, ℓ v < b := by
        by_contra h
        push Not at h
        have hge : b ≤ ℓ x := convexHull_min h ((convex_Ici b).linear_preimage ℓ.toLinearMap) hxs
        exact hxb.not_ge hge
      have hvK : v ∈ K.vertices := K.down_closed hs (Finset.singleton_subset_iff.mpr hv)
        (Finset.singleton_nonempty v)
      let U := V.filter (fun v => ℓ v ≤ b)
      have hvU : v ∈ U := Finset.mem_filter.mpr ⟨(hV v).mpr hvK, hvb.le⟩
      obtain ⟨p, hpU, hpmax⟩ := U.exists_max_image ℓ ⟨v, hvU⟩
      have hpK : p ∈ K.vertices := (hV p).mp (Finset.mem_filter.mp hpU).1
      have hpb : ℓ p ≤ b := (Finset.mem_filter.mp hpU).2
      by_cases hrest : (U.erase p).Nonempty
      · obtain ⟨q, hq, hqmax⟩ := (U.erase p).exists_max_image ℓ hrest
        have hqU := Finset.mem_of_mem_erase hq
        have hqK : q ∈ K.vertices := (hV q).mp (Finset.mem_filter.mp hqU).1
        have hqp : ℓ q < ℓ p := lt_of_le_of_ne (hpmax q hqU)
          (fun h => (Finset.ne_of_mem_erase hq) (hinj hqK hpK h))
        obtain ⟨a, hqa, hap⟩ := exists_between hqp
        have hab : a < b := hap.trans_le hpb
        have hbelowA : ∃ x ∈ frontier K.space, ℓ x < a :=
          (Topology.exists_mem_frontier_apply_lt_iff hcompact ℓ a).mpr
            ⟨q, K.vertices_subset_space hqK, hqa⟩
        have haboveA : ∃ x ∈ frontier K.space, a < ℓ x :=
          haboveB.imp fun _ hx => ⟨hx.1, hab.trans hx.2⟩
        have hsmallsub : V.filter (fun v => ℓ v ≤ a) ⊆ U := by
          intro v hv
          have hv' := Finset.mem_filter.mp hv
          exact Finset.mem_filter.mpr ⟨hv'.1, hv'.2.trans hab.le⟩
        have hpnot : p ∉ V.filter (fun v => ℓ v ≤ a) := fun h =>
          hap.not_ge (Finset.mem_filter.mp h).2
        have hsmall : (V.filter (fun v => ℓ v ≤ a)).card < n := by
          rw [← hn]
          exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
            ⟨hsmallsub, fun h => hpnot (h.symm ▸ hpU)⟩)
        have hleft := ih _ hsmall a rfl hbelowA haboveA
        have hgap (w : EuclideanSpace ℝ (Fin 3)) (hw : w ∈ K.vertices) (hwp : w ≠ p) :
            ℓ w < a ∨ b < ℓ w := by
          by_cases hwb : ℓ w ≤ b
          · exact Or.inl ((hqmax w (Finset.mem_erase.mpr
              ⟨hwp, Finset.mem_filter.mpr ⟨(hV w).mpr hw, hwb⟩⟩)).trans_lt hqa)
          · exact Or.inr (lt_of_not_ge hwb)
        have hbelowP : ∃ x ∈ frontier K.space, ℓ x < ℓ p :=
          hbelowA.imp fun _ hx => ⟨hx.1, hx.2.trans hap⟩
        have haboveP : ∃ x ∈ frontier K.space, ℓ p < ℓ x :=
          haboveB.imp fun _ hx => ⟨hx.1, hpb.trans_lt hx.2⟩
        have hslab := isSimplyEmbedded_frontier_slab_of_heightIndex_eq_zero_of_vertex_upper I K hK
            hS
          hreg hconn ℓ hℓ hinj hzero hpK hap
          (fun w hw hwp => (hgap w hw hwp).imp_right (fun h => hpb.trans_lt h)) hbelowA haboveP
        obtain ⟨ga, hga, hgaB⟩ := hfiber a hbelowA haboveA
        have hleftP := isSimplyEmbedded_frontier_sublevel_of_slab I hcompact.isClosed ℓ hℓ hap hleft
            hslab hga hgaB
        rcases hpb.lt_or_eq with hpb | hpb
        · have hslab' := isSimplyEmbedded_frontier_slab_of_heightIndex_eq_zero_of_vertex_lower I K
            hK hS
            hreg hconn ℓ hℓ hinj hzero hpK hpb
            (fun w hw hwp => (hgap w hw hwp).imp_left (fun h => h.trans hap)) hbelowP haboveB
          obtain ⟨gp, hgp, hgpB⟩ := hfiber (ℓ p) hbelowP haboveP
          exact isSimplyEmbedded_frontier_sublevel_of_slab I hcompact.isClosed ℓ hℓ hpb hleftP
              hslab' hgp hgpB
        · exact hpb ▸ hleftP
      · have hvp : v = p := by
          by_contra h
          exact hrest ⟨v, Finset.mem_erase.mpr ⟨h, hvU⟩⟩
        have hother : ∀ w ∈ K.vertices, w ≠ p → b < ℓ w := by
          intro w hw hwp
          by_contra h
          exact hrest ⟨w, Finset.mem_erase.mpr ⟨hwp,
            Finset.mem_filter.mpr ⟨(hV w).mpr hw, le_of_not_gt h⟩⟩⟩
        obtain ⟨gb, hgb, -⟩ := hfiber b ⟨x, hx, hxb⟩ haboveB
        exact isSimplyEmbedded_frontier_sublevel_of_lt_other_vertices I K ℓ.toLinearMap hpK
          (hvp ▸ hvb) hother ⟨gb, hgb⟩
  exact hrec _ r rfl hbelow habove

end DifferentialGeometry.Topology.PiecewiseLinear
