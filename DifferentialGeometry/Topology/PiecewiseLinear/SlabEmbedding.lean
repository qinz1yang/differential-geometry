/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ClosedStarCone
import DifferentialGeometry.Topology.PiecewiseLinear.SlabDeletionSequence

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem isSimplyEmbedded_frontier_slab_of_heightIndex_eq_zero_of_vertex_lower (I : SchoenfliesInput)
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hS : IsPLSphere 2 (frontier K.space))
    (hreg : closure (interior K.space) = K.space) (hconn : IsPreconnected (interior K.space))
    (ℓ : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices)
    (hzero : heightIndex (frontier K.space) ℓ = 0)
    {p : EuclideanSpace ℝ (Fin 3)} (hp : {p} ∈ K.faces) {b : ℝ} (hpb : ℓ p < b)
    (hgap : ∀ v ∈ K.vertices, v ≠ p → ℓ v < ℓ p ∨ b < ℓ v)
    (hbelow : ∃ x ∈ frontier K.space, ℓ x < ℓ p) (habove : ∃ y ∈ frontier K.space, b < ℓ y) :
    IsSimplyEmbedded (frontier (K.space ∩ ℓ ⁻¹' Icc (ℓ p) b)) := by
  classical
  let _ : DecidableEq (EuclideanSpace ℝ (Fin 3)) := Classical.decEq _
  have hslab := isPLSphere_frontier_slab_of_heightIndex_eq_zero K hK hS (by simp) hreg hconn
    ℓ hℓ hinj hzero hpb hbelow habove
  obtain ⟨_, _, _, _, g, hg, -⟩ := exists_isPLDiskDecomposition_fiber_of_heightIndex_eq_zero
    K hK hS (by simp) hreg hconn ℓ hℓ hinj hzero (ℓ p) hbelow
    (habove.imp fun _ hx => ⟨hx.1, hpb.trans hx.2⟩)
  refine ⟨hslab, ?_⟩
  intro W hWconv hW hSW
  obtain ⟨H, hH, hfix, himage⟩ := exists_isPLHomeomorphOn_frontier_slab_closedStar I K hK hS
    hreg hconn ℓ hℓ hinj hzero hp hpb ⟨le_rfl, hpb.le⟩ hgap hbelow habove hW hWconv hSW
  have hnew : IsPLSphere 2 (frontier (closedStar K p ∩ ℓ ⁻¹' Icc (ℓ p) b)) := by
    rw [← himage]
    exact hslab.of_isPLHomeomorphOn (hH.restrict hslab.isPolyhedron (subset_univ _))
  obtain ⟨L, hL, hLfin, hLball, hcone⟩ := exists_isPLBall_coneComplex_eq_closedStar_slab
    K hK (by simp) ℓ hℓ hinj hp hpb hgap ⟨g, hg⟩ hnew
  have hsimple : IsSimplyEmbedded (frontier (coneComplex hL).space) := by
    convert I.isSimplyEmbedded_frontier_coneComplex L p hL hLfin hLball using 1
    congr 1
    ext x
    simp only [mem_coneComplex_space_iff]
  rw [hcone] at hsimple
  have hnewW : frontier (closedStar K p ∩ ℓ ⁻¹' Icc (ℓ p) b) ⊆ W := by
    rw [← himage]
    rintro _ ⟨x, hx, rfl⟩
    by_contra hnot
    have heq : H x = x := H.injective (hfix hnot)
    exact hnot (heq.symm ▸ hSW hx)
  obtain ⟨T, G, hT, hcard, hG, hGimage, hGfix⟩ := hsimple.2 W hWconv hW hnewW
  refine ⟨T, H.trans G, hT, hcard, hH.trans hG, ?_, ?_⟩
  · change (G ∘ H) '' _ = _
    rw [image_comp, himage, hGimage]
  · intro x hx
    change G (H x) = x
    rw [hfix hx]
    exact hGfix hx

theorem isSimplyEmbedded_frontier_slab_of_heightIndex_eq_zero_of_vertex_upper (I : SchoenfliesInput)
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hS : IsPLSphere 2 (frontier K.space))
    (hreg : closure (interior K.space) = K.space) (hconn : IsPreconnected (interior K.space))
    (ℓ : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices)
    (hzero : heightIndex (frontier K.space) ℓ = 0)
    {p : EuclideanSpace ℝ (Fin 3)} (hp : {p} ∈ K.faces) {a : ℝ} (hap : a < ℓ p)
    (hgap : ∀ v ∈ K.vertices, v ≠ p → ℓ v < a ∨ ℓ p < ℓ v)
    (hbelow : ∃ x ∈ frontier K.space, ℓ x < a) (habove : ∃ y ∈ frontier K.space, ℓ p < ℓ y) :
    IsSimplyEmbedded (frontier (K.space ∩ ℓ ⁻¹' Icc a (ℓ p))) := by
  have hzero' : heightIndex (frontier K.space) (-ℓ) = 0 := by
    have heq : heightIndex (frontier K.space) (-ℓ) = heightIndex (frontier K.space) ℓ := by
      change heightIndex (frontier K.space) (fun x => -ℓ x) = heightIndex (frontier K.space) ℓ
      have hsing : heightSingularPoints (frontier K.space) (fun x => -ℓ x) =
          heightSingularPoints (frontier K.space) ℓ := by
        ext x
        simp only [heightSingularPoints, neg_inj]
      rw [heightIndex, heightIndex, hsing]
      apply tsum_congr
      intro x
      simp only [levelPolygons, neg_inj]
    exact heq.trans hzero
  have hinj' : InjOn (-ℓ) K.vertices :=
    fun _ hx _ hy h => hinj hx hy (neg_injective h)
  have hgap' : ∀ v ∈ K.vertices, v ≠ p → (-ℓ) v < (-ℓ) p ∨ -a < (-ℓ) v := by
    intro v hv hne
    rcases hgap v hv hne with h | h
    · exact Or.inr (neg_lt_neg h)
    · exact Or.inl (neg_lt_neg h)
  have h := isSimplyEmbedded_frontier_slab_of_heightIndex_eq_zero_of_vertex_lower I K hK hS hreg
      hconn
    (-ℓ) (neg_ne_zero.mpr hℓ) hinj' hzero' hp (neg_lt_neg hap) hgap'
    (habove.imp fun _ hx => ⟨hx.1, neg_lt_neg hx.2⟩)
    (hbelow.imp fun _ hx => ⟨hx.1, neg_lt_neg hx.2⟩)
  have hset : (-ℓ) ⁻¹' Icc ((-ℓ) p) (-a) = ℓ ⁻¹' Icc a (ℓ p) := by
    ext x
    simp only [mem_preimage, mem_Icc, neg_apply, neg_le_neg_iff]
    exact and_comm
  rwa [hset] at h

end DifferentialGeometry.Topology.PiecewiseLinear
