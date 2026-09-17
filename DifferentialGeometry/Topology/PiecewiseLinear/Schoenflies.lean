import DifferentialGeometry.Topology.PiecewiseLinear.SublevelEmbedding
import DifferentialGeometry.Topology.PiecewiseLinear.HeightFilling
import DifferentialGeometry.Topology.PiecewiseLinear.SchoenfliesReduction

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem isSimplyEmbedded_frontier_of_heightIndex_eq_zero (I : SchoenfliesInput)
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hS : IsPLSphere 2 (frontier K.space))
    (hreg : closure (interior K.space) = K.space) (hconn : IsPreconnected (interior K.space))
    (ℓ : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices)
    (hzero : heightIndex (frontier K.space) ℓ = 0) : IsSimplyEmbedded (frontier K.space) := by
  classical
  have hcompact := (isPolyhedron_space K).isCompact
  have hne : K.space.Nonempty := hS.nonempty.mono hcompact.isClosed.frontier_subset
  obtain ⟨v₀, -, p, hp, hbound, -, -⟩ := exists_extreme_height_fibers K hne ℓ.toLinearMap hinj
  obtain ⟨s, hs, hps, hcard⟩ := hK.exists_face_superset_card_eq hp
  have hpS : p ∈ s := hps (Finset.mem_singleton_self p)
  have herase : (s.erase p).Nonempty := Finset.card_pos.mp (by
    rw [Finset.card_erase_of_mem hpS, hcard]
    norm_num)
  obtain ⟨v, hv⟩ := herase
  have hvK : v ∈ K.vertices := K.down_closed hs
    (Finset.singleton_subset_iff.mpr (Finset.mem_of_mem_erase hv)) (Finset.singleton_nonempty v)
  obtain ⟨q, hq, hqmax⟩ := Set.exists_max_image (K.vertices \ {p}) ℓ
    (SimplicialComplex.finite_vertices K).sdiff ⟨v, hvK, Finset.ne_of_mem_erase hv⟩
  have hqp : ℓ q < ℓ p := lt_of_le_of_ne (hbound q (K.vertices_subset_space hq.1)).2
    (fun h => hq.2 (hinj hq.1 hp h))
  obtain ⟨r, hqr, hrp⟩ := exists_between hqp
  have hother : ∀ v ∈ K.vertices, v ≠ p → ℓ v < r :=
    fun v hv hvp => (hqmax v ⟨hv, hvp⟩).trans_lt hqr
  have hbelow : ∃ x ∈ frontier K.space, ℓ x < r :=
    (Topology.exists_mem_frontier_apply_lt_iff hcompact ℓ r).mpr
      ⟨q, K.vertices_subset_space hq.1, hqr⟩
  have habove : ∃ x ∈ frontier K.space, r < ℓ x :=
    (Topology.exists_mem_frontier_lt_apply_iff hcompact ℓ r).mpr
      ⟨p, K.vertices_subset_space hp, hrp⟩
  obtain ⟨-, -, -, -, g, hg, hgb⟩ := exists_isPLDiskDecomposition_fiber_of_heightIndex_eq_zero
    K hK hS (by simp) hreg hconn ℓ hℓ hinj hzero r hbelow habove
  have hleft := isSimplyEmbedded_frontier_sublevel_of_heightIndex_eq_zero I K hK hS hreg hconn
    ℓ hℓ hinj hzero r hbelow habove
  have hright := isSimplyEmbedded_frontier_superlevel_of_other_vertices_lt I K ℓ.toLinearMap hp
    hrp hother ⟨g, hg⟩
  exact isSimplyEmbedded_frontier_of_sublevel_superlevel I hcompact.isClosed ℓ hℓ r hleft hright hg hgb

theorem isSimplyEmbedded_of_heightIndex_eq_zero (I : SchoenfliesInput)
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite K.faces]
    (hK : IsPLSphere 2 K.space) (ℓ : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
    (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices) (hzero : heightIndex K.space ℓ = 0) :
    IsSimplyEmbedded K.space := by
  obtain ⟨R, f, hRfin, hRman, -, hRfront, hRcl, hRconn, -, -, hfne, hfinj, hfzero, -⟩ :=
    exists_filling_injOn_vertices_of_heightIndex_eq_zero K hK (by simp) ℓ hℓ hinj hzero
      (show (0 : ℝ) < 1 by norm_num)
  let _ : Finite R.faces := hRfin.to_subtype
  have hS : IsPLSphere 2 (frontier R.space) := hRfront.symm ▸ hK
  have hzeroR : heightIndex (frontier R.space) f = 0 := by rwa [hRfront]
  have h := isSimplyEmbedded_frontier_of_heightIndex_eq_zero I R hRman hS hRcl
    hRconn.isPreconnected f hfne hfinj hzeroR
  rwa [hRfront] at h

theorem isSimplyEmbedded_of_isPLSphere_two (I : SchoenfliesInput)
    {S : Set (EuclideanSpace ℝ (Fin 3))} (hS : IsPLSphere 2 S) : IsSimplyEmbedded S := by
  apply isSimplyEmbedded_of_heightIndex_zero_case I ?_ hS
  intro K hKfin hK ℓ hℓ hinj hzero
  let _ : Finite K.faces := hKfin
  exact isSimplyEmbedded_of_heightIndex_eq_zero I K hK ℓ hℓ hinj hzero

theorem exists_isPLBall_of_isPLSphere_two (I : SchoenfliesInput)
    {S : Set (EuclideanSpace ℝ (Fin 3))} (hS : IsPLSphere 2 S) :
    ∃ B : Set (EuclideanSpace ℝ (Fin 3)), IsPLBall 3 B ∧ frontier B = S ∧ Bornology.IsBounded B := by
  obtain ⟨B, hB, hfront, hbounded, -⟩ :=
    exists_hasPushProperty_of_isSimplyEmbedded (isSimplyEmbedded_of_isPLSphere_two I hS)
  exact ⟨B, hB, hfront, hbounded⟩

end DifferentialGeometry.Topology.PiecewiseLinear
