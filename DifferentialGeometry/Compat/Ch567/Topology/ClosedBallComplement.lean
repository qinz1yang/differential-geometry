import DifferentialGeometry.Topology.ClosedBallComplement
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-!
# PORT567 foundation supplement: complements of finitely many chart balls

The later PC layout's `Topology/ClosedBallComplement.lean` (source
`differential-geometry-baseline@6fb7f5946`, sha256 `8e2baac6…dfffc`) contains, in addition to
the content of the integration-layout file of the same path, the declarations
`exists_connected_collars_image_closedBall` (private), `isPreconnected_compl_iUnion_image_closedBall`
and `isPathConnected_compl_iUnion_image_closedBall`. They are reproduced here verbatim
(source lines 43–146, same namespace and variables); every other declaration they use
(`isConnected_ball_sdiff_closedBall`, `isPreconnected_compl_iUnion_of_collar`) has the same
statement in the integration layout (`ClosedBallComplement`, `ConnectedSum/BallMarking`).
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric
open scoped Topology

namespace DifferentialGeometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem exists_connected_collars_image_closedBall
    [ProperSpace E] {M : Type*} [TopologicalSpace M] [T2Space M]
    {ι : Type*} [Finite ι] (e : ι → OpenPartialHomeomorph E M) (r : ι → ℝ)
    (hdim : 1 < Module.rank ℝ E) (hr : ∀ i, 0 ≤ r i)
    (hs : ∀ i, Metric.closedBall 0 (r i) ⊆ (e i).source)
    (hdisj : ∀ i j, i ≠ j →
      Disjoint (e i '' Metric.closedBall 0 (r i)) (e j '' Metric.closedBall 0 (r j))) :
    ∃ V : ι → Set M, (∀ i, IsOpen (V i)) ∧
      (∀ i, e i '' Metric.closedBall 0 (r i) ⊆ V i) ∧
      (∀ i j, i ≠ j → Disjoint (V i) (e j '' Metric.closedBall 0 (r j))) ∧
      ∀ i, IsConnected (V i \ e i '' Metric.closedBall 0 (r i)) := by
  classical
  let K (i : ι) : Set M := e i '' Metric.closedBall 0 (r i)
  have hK (i : ι) : IsCompact (K i) :=
    (isCompact_closedBall (0 : E) (r i)).image_of_continuousOn
      ((e i).continuousOn_toFun.mono (hs i))
  let L (i : ι) : Set M := ⋃ j : {j : ι // j ≠ i}, K j.val
  have hL (i : ι) : IsClosed (L i) :=
    isClosed_iUnion_of_finite fun j => (hK j.val).isClosed
  have hsub (i : ι) : Metric.closedBall 0 (r i) ⊆
      (e i).source ∩ (e i) ⁻¹' (L i)ᶜ := by
    intro x hx
    refine ⟨hs i hx, ?_⟩
    change e i x ∉ L i
    intro hxL
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxL
    exact Set.disjoint_left.mp (hdisj i j.val (Ne.symm j.property)) ⟨x, hx, rfl⟩ hj
  have hR (i : ι) : ∃ R : ℝ, r i < R ∧
      Metric.ball 0 R ⊆ (e i).source ∩ (e i) ⁻¹' (L i)ᶜ := by
    have ho : IsOpen ((e i).source ∩ (e i) ⁻¹' (L i)ᶜ) :=
      (e i).isOpen_inter_preimage (hL i).isOpen_compl
    obtain ⟨δ, hδ, hδsub⟩ :=
      (isCompact_closedBall (0 : E) (r i)).exists_thickening_subset_open ho (hsub i)
    rw [thickening_closedBall hδ (hr i)] at hδsub
    refine ⟨r i + δ / 2, by linarith only [hδ], ?_⟩
    exact (Metric.ball_subset_ball (by linarith only [hδ] : r i + δ / 2 ≤ δ + r i)).trans hδsub
  choose R hRlt hRs using hR
  let V (i : ι) : Set M := e i '' Metric.ball 0 (R i)
  have hopen (i : ι) : IsOpen (V i) :=
    (e i).isOpen_image_of_subset_source Metric.isOpen_ball (fun x hx => (hRs i hx).1)
  have hKV (i : ι) : K i ⊆ V i :=
    Set.image_mono (Metric.closedBall_subset_ball (hRlt i))
  have hVK (i j : ι) (hij : i ≠ j) : Disjoint (V i) (K j) := by
    rw [Set.disjoint_left]
    rintro y ⟨x, hx, rfl⟩ hy
    exact (hRs i hx).2 (Set.mem_iUnion.mpr ⟨⟨j, Ne.symm hij⟩, hy⟩)
  have hconn (i : ι) : IsConnected (V i \ K i) := by
    have hinj : Set.InjOn (e i) (Metric.ball 0 (R i)) :=
      (e i).injOn.mono (fun x hx => (hRs i hx).1)
    have heq := hinj.image_sdiff_subset (Metric.closedBall_subset_ball (hRlt i))
    change e i '' (Metric.ball 0 (R i) \ Metric.closedBall 0 (r i)) = V i \ K i at heq
    rw [← heq]
    exact (isConnected_ball_sdiff_closedBall hdim (hr i) (hRlt i)).image _
      ((e i).continuousOn_toFun.mono (fun x hx => (hRs i hx.1).1))
  exact ⟨V, hopen, hKV, hVK, hconn⟩

theorem isPreconnected_compl_iUnion_image_closedBall
    [ProperSpace E] {M : Type*} [TopologicalSpace M] [T2Space M] [PreconnectedSpace M]
    {ι : Type*} [Finite ι] (e : ι → OpenPartialHomeomorph E M) (r : ι → ℝ)
    (hdim : 1 < Module.rank ℝ E) (hr : ∀ i, 0 ≤ r i)
    (hs : ∀ i, Metric.closedBall 0 (r i) ⊆ (e i).source)
    (hdisj : ∀ i j, i ≠ j →
      Disjoint (e i '' Metric.closedBall 0 (r i)) (e j '' Metric.closedBall 0 (r j))) :
    IsPreconnected ((⋃ i, e i '' Metric.closedBall 0 (r i))ᶜ : Set M) := by
  obtain ⟨V, hV, hKV, hVK, hconn⟩ :=
    exists_connected_collars_image_closedBall e r hdim hr hs hdisj
  have hK (i : ι) : IsClosed (e i '' Metric.closedBall 0 (r i)) :=
    ((isCompact_closedBall (0 : E) (r i)).image_of_continuousOn
      ((e i).continuousOn_toFun.mono (hs i))).isClosed
  exact isPreconnected_compl_iUnion_of_collar
    (fun i => e i '' Metric.closedBall 0 (r i)) V hK hV hKV hVK hconn

theorem isPathConnected_compl_iUnion_image_closedBall
    [ProperSpace E] {M : Type*} [TopologicalSpace M] [T2Space M]
    [ConnectedSpace M] [LocallyPathConnectedSpace M]
    {ι : Type*} [Finite ι] (e : ι → OpenPartialHomeomorph E M) (r : ι → ℝ)
    (hdim : 1 < Module.rank ℝ E) (hr : ∀ i, 0 ≤ r i)
    (hs : ∀ i, Metric.closedBall 0 (r i) ⊆ (e i).source)
    (hdisj : ∀ i j, i ≠ j →
      Disjoint (e i '' Metric.closedBall 0 (r i)) (e j '' Metric.closedBall 0 (r j))) :
    IsPathConnected ((⋃ i, e i '' Metric.closedBall 0 (r i))ᶜ : Set M) := by
  classical
  obtain ⟨V, hV, hKV, hVK, hconn⟩ :=
    exists_connected_collars_image_closedBall e r hdim hr hs hdisj
  have hK (i : ι) : IsClosed (e i '' Metric.closedBall 0 (r i)) :=
    ((isCompact_closedBall (0 : E) (r i)).image_of_continuousOn
      ((e i).continuousOn_toFun.mono (hs i))).isClosed
  have hpre := isPreconnected_compl_iUnion_of_collar
    (fun i => e i '' Metric.closedBall 0 (r i)) V hK hV hKV hVK hconn
  have hne : ((⋃ i, e i '' Metric.closedBall 0 (r i))ᶜ : Set M).Nonempty := by
    rcases isEmpty_or_nonempty ι with hI | hI
    · refine ⟨Classical.arbitrary M, ?_⟩
      simp only [mem_compl_iff, mem_iUnion, not_exists]
      exact fun i => isEmptyElim i
    · obtain ⟨i⟩ := hI
      obtain ⟨x, hx⟩ := (hconn i).nonempty
      refine ⟨x, ?_⟩
      intro hmem
      obtain ⟨j, hj⟩ := mem_iUnion.mp hmem
      by_cases hji : j = i
      · exact hx.2 (hji ▸ hj)
      · exact Set.disjoint_left.mp (hVK i j (Ne.symm hji)) hx.1 hj
  exact (isClosed_iUnion_of_finite hK).isOpen_compl.isConnected_iff_isPathConnected.mp
    ⟨hne, hpre⟩
end DifferentialGeometry.Topology
