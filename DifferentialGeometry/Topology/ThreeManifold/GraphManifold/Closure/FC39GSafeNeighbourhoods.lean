import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Adapted
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GSafeRows

/-!
# FC39 GROUP G, target `stub_exists_safeNeighbourhoods` (lane FC39-G-SAFE)

The frozen target `T:313–315` (`docs/geometrization/chapter14/evidence/fc39-p0/Targets.lean.txt`),
proved as a general theorem on the contract (external review 56, D56-1; route: external draft
task 58 §一 S1–S7, dispositions D58-2; lane sheet `build-logs/resume/sheet-FC39-G-SAFE.md`):

* `exists_sharedSafe_GSAFE` (S4) — safe open neighbourhoods of the actual shared faces: the
  shared sets are compact and pairwise disjoint, and avoid the closed obstacle
  `edgePiece ∪ region ∪ ⋃ i, closure (E.collar i).target` (`FC39GSafeRows.lean`, S2–S3); the
  finite closure separation of `FC39GSafeTopology.lean` gives pairwise disjoint closures off it;
* `exists_safeNeighbourhoods_GSAFE` (S7) — **the frozen statement verbatim**: the shared
  neighbourhoods are chosen FIRST; the rim base points of the endpoints are pairwise distinct
  (`rimBase_injective_GSAFE`) and get pairwise disjoint open neighbourhoods `D`; inside
  `D ∩ labelledTubes.base e` the ambient-closure shrinking of saturated tubes
  (`CircleBundle.exists_tube_closure_subset_GSAFE`) keeps the closure of each corner tube off the
  closures of the shared neighbourhoods and of the port collars (the whole fibre is the rim, which
  lies in the edge piece and avoids the port-collar closures), and inside `tube (D e)`.

The final `ProtectionLayer`, seam collars, global face functions and any width hypothesis are
NOT used.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}

/-- **S4: safe neighbourhoods of the actual shared faces.** -/
theorem exists_sharedSafe_GSAFE (Rw : FC39RowsV2 W E) :
    ∃ N : Rw.SharedFace → TopologicalSpace.Opens W.Carrier, SharedSafe Rw N := by
  have := Rw.finite_sharedFace_GSAFE
  have hB : IsClosed (Rw.edge.edgePiece ∪ Rw.circle.region ∪
      ⋃ i, closure (E.collar i).target) :=
    ((Rw.edge.proper Rw.edge.cbase Rw.edge.cbase_compact).isClosed.union
      Rw.isClosed_region_GSAFE).union
      (isClosed_iUnion_of_finite fun _ => isClosed_closure)
  obtain ⟨U, hU, hKU, hdisj, hUB⟩ := exists_closure_separation_GSAFE (fun σ => Rw.sharedSet σ)
    (fun σ => (Rw.isCompact_sharedSet_GSAFE σ).isClosed) Rw.sharedSet_pairwise_disjoint_GSAFE hB
    (fun σ => Disjoint.union_right
      (Disjoint.union_right (Rw.sharedSet_disjoint_edgePiece_GSAFE σ)
        (Rw.sharedSet_disjoint_region_GSAFE σ))
      (disjoint_iUnion_right.2 fun i => Rw.sharedSet_disjoint_closure_collar_GSAFE σ i))
  refine ⟨fun σ => ⟨U σ, hU σ⟩, ?_⟩
  exact
    { face_subset := hKU
      closure_disjoint := hdisj
      off_edge := fun σ => (hUB σ).mono_right (subset_union_left.trans subset_union_left)
      off_region := fun σ => (hUB σ).mono_right (subset_union_right.trans subset_union_left)
      off_external := fun σ i => (hUB σ).mono_right (subset_closure.trans
        ((subset_iUnion (fun i => closure (E.collar i).target) i).trans subset_union_right)) }

/-- **`stub_exists_safeNeighbourhoods` (`T:313–315`), the frozen statement verbatim.** -/
theorem exists_safeNeighbourhoods_GSAFE (Rw : FC39RowsV2 W E) :
    Nonempty (ProducerSafeNeighbourhoods Rw) := by
  obtain ⟨N, hN⟩ := exists_sharedSafe_GSAFE Rw
  have := Rw.finite_edgeEnd_GSAFE
  have := Rw.finite_sharedFace_GSAFE
  let pt : Rw.edge.EdgeEnd → Rw.circle.Base := fun e => Rw.junctions.rimBase e.1
  obtain ⟨D, hD, hDdisj⟩ := Set.Finite.t2_separation (Set.finite_range pt)
  have hO : IsOpen ((⋃ σ, closure (N σ : Set W.Carrier)) ∪
      ⋃ i, closure (E.collar i).target)ᶜ :=
    ((isClosed_iUnion_of_finite fun _ => isClosed_closure).union
      (isClosed_iUnion_of_finite fun _ => isClosed_closure)).isOpen_compl
  have hfib : ∀ e, Rw.circle.fibre (pt e) ⊆
      ((⋃ σ, closure (N σ : Set W.Carrier)) ∪ ⋃ i, closure (E.collar i).target)ᶜ := by
    intro e x hx hxO
    rcases hxO with h | h
    · obtain ⟨σ, hσ⟩ := mem_iUnion.1 h
      have hc := Rw.edge.mem_cbase_of_edgeEnd_GSAFE e
      have hxr : x ∈ Rw.edge.rim e.1 := by
        rw [Rw.junctions.rim_fibre e.1 hc]
        exact hx
      exact Set.disjoint_left.1 (hN.off_edge σ) hσ
        (Rw.edge.disk_subset_edgePiece_GSAFE hc (Rw.edge.rim_subset_disk_GSAFE _ hxr))
    · obtain ⟨i, hi⟩ := mem_iUnion.1 h
      exact Set.disjoint_left.1 (Rw.fibre_rimBase_disjoint_closure_collar_GSAFE e i) hx hi
  have hV : ∀ e, ∃ V : Set Rw.circle.Base, IsOpen V ∧ pt e ∈ V ∧
      V ⊆ D (pt e) ∩ Rw.labelledTubes.base e ∧
      closure (Rw.circle.tube V) ⊆
        ((⋃ σ, closure (N σ : Set W.Carrier)) ∪ ⋃ i, closure (E.collar i).target)ᶜ ∩
          Rw.circle.tube (D (pt e) ∩ Rw.labelledTubes.base e) := fun e =>
    Rw.circle.exists_tube_closure_subset_GSAFE (pt e) hO (hfib e)
      ((hD (pt e)).2.inter (Rw.labelledTubes.base e).isOpen)
      ⟨(hD (pt e)).1, Rw.labelledTubes.rimBase_mem e⟩
  choose V hVo hVm hVsub hVcl using hV
  refine ⟨
    { shared := N
      shared_safe := hN
      cornerBase := fun e => ⟨V e, hVo e⟩
      cornerBase_sub := fun e => (hVsub e).trans inter_subset_right
      rimBase_mem := hVm
      corner_closure_disjoint := ?_
      corner_off_external := ?_
      corner_off_shared := ?_ }⟩
  · intro e e' hee
    have hpt : pt e ≠ pt e' := fun h => hee (Rw.rimBase_injective_GSAFE h)
    have hDD : Disjoint (D (pt e)) (D (pt e')) :=
      hDdisj (mem_range_self e) (mem_range_self e') hpt
    exact (Rw.circle.tube_disjoint_GSAFE hDD).mono
      ((hVcl e).trans (inter_subset_right.trans (Rw.circle.tube_mono_GSAFE inter_subset_left)))
      ((hVcl e').trans (inter_subset_right.trans (Rw.circle.tube_mono_GSAFE inter_subset_left)))
  · intro e i
    refine Set.disjoint_left.2 fun x hx hxi => ?_
    exact (hVcl e hx).1 (Or.inr (mem_iUnion.2 ⟨i, subset_closure hxi⟩))
  · intro e σ
    refine Set.disjoint_left.2 fun x hx hxσ => ?_
    exact (hVcl e hx).1 (Or.inl (mem_iUnion.2 ⟨σ, hxσ⟩))

end GC.GraphManifold.Assembly.FC39P0
