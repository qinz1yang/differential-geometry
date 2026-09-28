/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CyclicBallMeridians
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactFaceCycle
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTraceSeams

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C V : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3} {h f₁ : E3 → E3} {ε : ℝ}
  {H : Finset E3 → Set E3}

theorem Section34CompactCutFrame.splitDiskBoundary_is_essential
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src)) (s : Section34CompactSimplexIndex K 3)
    (e : Section34CompactEdgeIndex K K') (he : Section34Incident e.1 s.1) :
    IsConnected (frontier (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s) \
      section34CompactSplitDiskImage srcBd f₁ e) ∧
      ¬ ∃ (D : Set E3) (r : (Fin 3 → ℝ) → E3),
        IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧
          D ⊆ frontier (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s) ∧
          section34CompactSplitDiskImage srcBd f₁ e = r '' stdSimplexBoundary 2 := by
  obtain ⟨n, v, -, -, hadj, hnext, hedge, htriple, hU⟩ :=
    exists_cycle_order_compact_face_vertex_balls hcut hf₁ s
  let B := fun i => section34CompactVertexBallImage src f₁ (v i)
  have hB : ∀ i, IsPLBall 3 (B i) :=
    fun i => (hcut.isPLCellOn_vertexBallImage hf₁ (v i)).isPLBall_three
  have hnextB : ∀ i j, (SimpleGraph.cycleGraph (n + 3)).Adj i j → IsPLBall 2 (B i ∩ B j) := by
    intro i j hij
    obtain ⟨d, -, hD⟩ := hnext i j hij
    obtain ⟨q, hq, -⟩ := (hcut.isPLCellOn_splitDiskImage hf₁ d).exists_isPLHomeomorphOn_stdSimplex
    exact hD ▸ (show IsPLBall 2 (section34CompactSplitDiskImage src f₁ d) from ⟨q, hq⟩)
  have hdisB : ∀ i j, i ≠ j → ¬ (SimpleGraph.cycleGraph (n + 3)).Adj i j →
      Disjoint (B i) (B j) := by
    intro i j hij hno
    exact Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp
      (fun hnon => hno ((hadj i j hij).mpr hnon)))
  obtain ⟨i, j, hij, hD⟩ := hedge e he
  obtain ⟨q, hq, hqb⟩ := (hcut.isPLCellOn_splitDiskImage hf₁ e).exists_isPLHomeomorphOn_stdSimplex
  have hess := cyclic_ball_seam_is_essential B hB hnextB hdisB htriple hij (hD ▸ hq)
  dsimp only [B] at hess
  rwa [hU, ← hqb] at hess

theorem split_disks_form_marked_meridian_system
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    (s : Section34CompactSimplexIndex K 3) :
    ∃ (J Q : Set E3) (f : E3 × E3 → E3)
      (p : {e : Section34CompactEdgeIndex K K' // Section34Incident e.1 s.1} → E3),
      IsPLSphere 1 J ∧ IsPLSphere 1 Q ∧
      IsPLHomeomorphOn f (J ×ˢ Q)
        (frontier (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s)) ∧
      (∀ e, p e ∈ Q) ∧ Function.Injective p ∧
      (∀ e, section34CompactSplitDiskImage srcBd f₁ e.1 = f '' (J ×ˢ {p e})) ∧
      ∀ e : {e : Section34CompactEdgeIndex K K' // Section34Incident e.1 s.1},
        section34CompactSplitDiskImage src f₁ e.1 ⊆
            section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s ∧
          frontier (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s) ∩
            section34CompactSplitDiskImage src f₁ e.1 =
              section34CompactSplitDiskImage srcBd f₁ e.1 ∧
          section34CompactSplitDiskImage src f₁ e.1 \ section34CompactSplitDiskImage srcBd f₁ e.1 ⊆
            interior (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s) := by
  classical
  have := finite_section34CompactGraphIndex hcut.2.2.1 (section34CompactGraphSkeleton K) 2
  obtain ⟨-, hf₁, -, -, -, -, -, -, hnest, -⟩ := id hgraph
  obtain ⟨-, -, -, -, hT, -⟩ := hnest s
  let I := {e : Section34CompactEdgeIndex K K' // Section34Incident e.1 s.1}
  let _ : Fintype I := Fintype.ofFinite I
  obtain ⟨n, v, -, hv, -⟩ := exists_cycle_order_compact_face_vertex_balls hcut hf₁ s
  have hv0 := (hv (v 0)).mpr ⟨0, rfl⟩
  obtain ⟨e₁, e₂, hne, he₁, he₂, -⟩ :=
    exists_section34CompactEdgeIndex_pair_of_incident hcut.2.2.2.2.1 hcut.2.2.1 s (v 0) hv0
  have hneI : (⟨e₁, he₁⟩ : I) ≠ ⟨e₂, he₂⟩ := fun h => hne (congrArg Subtype.val h)
  have hcard : 1 < Fintype.card I := by
    have hle := Finset.card_le_card (Finset.subset_univ ({⟨e₁, he₁⟩, ⟨e₂, he₂⟩} : Finset I))
    rw [Finset.card_pair hneI, Finset.card_univ] at hle
    omega
  let a := Fintype.equivFin I
  let G := fun i => section34CompactSplitDiskImage srcBd f₁ (a.symm i).1
  have hG : ∀ i, IsPLSphere 1 (G i) :=
    fun i => (hcut.isPLCellOn_splitDiskImage hf₁ (a.symm i).1).isPLSphere_one_of_two
  have hGΘ : ∀ i, G i ⊆
      frontier (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s) := by
    intro i x hx
    exact ((hcut.splitDiskImage_faceTorus_boundary hf₁ s (a.symm i).1
      (a.symm i).2).2.1.symm.subset hx).1
  have hdisj : Pairwise fun i j => Disjoint (G i) (G j) := by
    intro i j hij
    apply (hcut.disjoint_splitDiskImage hf₁ (fun h => hij (a.symm.injective (Subtype.ext h)))).mono
      (hcut.isPLCellOn_splitDiskImage hf₁ (a.symm i).1).boundary_subset
      (hcut.isPLCellOn_splitDiskImage hf₁ (a.symm j).1).boundary_subset
  have hess := fun i => (hcut.splitDiskBoundary_is_essential hf₁ s (a.symm i).1 (a.symm i).2).2
  obtain ⟨J, Q, f, q, hJ, hQ, hf, hqQ, hqinj, hGq⟩ :=
    exists_product_coordinates_for_disjoint_essential_polygons hT G hcard hG hGΘ hdisj hess
  refine ⟨J, Q, f, q ∘ a, hJ, hQ, hf, fun e => hqQ (a e), hqinj.comp a.injective, ?_, ?_⟩
  · intro e
    simpa only [G, a.symm_apply_apply, Function.comp_apply] using hGq (a e)
  · intro e
    exact hcut.splitDiskImage_faceTorus_boundary hf₁ s e.1 e.2

end DifferentialGeometry.Topology.PiecewiseLinear
