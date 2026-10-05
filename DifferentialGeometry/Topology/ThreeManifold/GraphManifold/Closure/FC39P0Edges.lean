import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Base
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Layers

/-!
# FC39 producer, packet P0 (gate 1), §1: edge registration by actual components

Task-47 draft §1 (disposition D4): the old `EdgeLink` (union of handle images, end disks over some
endpoint, slice rims over some base point) allowed one actual component to be registered twice
(regression test A). It is replaced by

* `EdgeComponentModels P` — the NEW export of the edge bundle: finitely many interval and circle
  components of the closed base `C₂` (`componentEquiv`), their smooth parametrizations with image
  EXACTLY the component, the endpoint bijection `Fin intervalCount × Bool ≃ EdgeEnd P`, and per
  component a WHOLE fibre-preserving product (`D² × [0, 1]` as an `EdgeHandle`, resp. `D² × S¹`,
  open choice 2: the direct product, no mapping-torus intermediate) onto `wholeComponent`, whose
  slices are the whole disks / rims;
* `EdgeComponentsLink P M H` — the handles and edge-circle pieces of an `EdgeLayer` in bijection
  with the interval / circle components, each image the WHOLE component, with the projection, disk
  and rim of every slice.

The disjointness clauses that the dry stubs S4 / S9 needed are DERIVED here, not assumed:
`handle_ranges_disjoint_of_components`, `endDisks_disjoint_of_components` (including the two ends
of one handle), and the analogous edge-circle clauses; `iUnion_ranges_eq_edgePiece` gives the old
union equation.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

local instance diskChartsEdges_FC39P0 : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

variable {W : CompactCarrier.{u}}

/-- **§1.1 The component export of the edge bundle (NEW export / transport).** Finitely many
nondegenerate closed interval components and circle components of `C₂`; smooth embeddings with
image exactly the component; the endpoint bijection with value exactly `intervalBase i (iccEnd b)`;
per interval component a WHOLE `D² × [0, 1]` parametrization (smooth, injective, full rank:
an `EdgeHandle`) onto `wholeComponent`, projecting to `intervalBase i t` with slice image the whole
disk and slice rim the whole rim; per circle component the same with `D² × S¹` (fibre-preserving
product of FC37's orientable disk bundle). The bijection of the labels with the actual components
of the edge piece is NOT a field: it is derived (`Targets.lean`, `stub_totalComponentEquiv`). -/
structure EdgeComponentModels (P : EdgeBundle W) where
  intervalCount : ℕ
  circleCount : ℕ
  componentEquiv : (Fin intervalCount ⊕ Fin circleCount) ≃ P.EdgeBaseComponent
  intervalBase : Fin intervalCount → Icc (0 : ℝ) 1 → P.Base
  intervalBase_embedding : ∀ i, IsSmoothEmbedding (𝓡∂ 1) (𝓡 1) ∞ (intervalBase i)
  intervalBase_range : ∀ i, range (intervalBase i) = (componentEquiv (.inl i)).1
  circleBase : Fin circleCount → Circle → P.Base
  circleBase_embedding : ∀ j, IsSmoothEmbedding (𝓡 1) (𝓡 1) ∞ (circleBase j)
  circleBase_range : ∀ j, range (circleBase j) = (componentEquiv (.inr j)).1
  endpointEquiv : (Fin intervalCount × Bool) ≃ P.EdgeEnd
  endpointEquiv_apply : ∀ i b, (endpointEquiv (i, b)).1 = intervalBase i (iccEnd b)
  intervalTriv : Fin intervalCount → EdgeHandle W
  intervalTriv_range : ∀ i,
    range (intervalTriv i).map = P.wholeComponent (componentEquiv (.inl i))
  intervalTriv_proj : ∀ i w t, ∃ hx : (intervalTriv i).map (w, t) ∈ P.source,
    P.proj ⟨(intervalTriv i).map (w, t), hx⟩ = intervalBase i t
  intervalTriv_disk : ∀ i t,
    range (fun w => (intervalTriv i).map (w, t)) = P.disk (intervalBase i t)
  intervalTriv_rim : ∀ i t,
    (fun w => (intervalTriv i).map (w, t)) '' diskRim = P.rim (intervalBase i t)
  circleTriv : Fin circleCount → ClosedCell 2 × Circle → W.Carrier
  circleTriv_smooth : ∀ j, ContMDiff ((𝓡∂ 2).prod (𝓡 1)) W.model ∞ (circleTriv j)
  circleTriv_mfderiv : ∀ j p,
    Bijective (mfderiv ((𝓡∂ 2).prod (𝓡 1)) W.model (circleTriv j) p)
  circleTriv_injective : ∀ j, Injective (circleTriv j)
  circleTriv_range : ∀ j, range (circleTriv j) = P.wholeComponent (componentEquiv (.inr j))
  circleTriv_proj : ∀ j w z, ∃ hx : circleTriv j (w, z) ∈ P.source,
    P.proj ⟨circleTriv j (w, z), hx⟩ = circleBase j z
  circleTriv_disk : ∀ j z, range (fun w => circleTriv j (w, z)) = P.disk (circleBase j z)
  circleTriv_rim : ∀ j z, (fun w => circleTriv j (w, z)) '' diskRim = P.rim (circleBase j z)

/-- **§1.2 The new edge link.** Handles and edge-circle pieces in bijection with the actual interval
and circle components; every image is the WHOLE inverse image of its component; every slice
projects to the component's parametrization and its image / rim is the whole disk / rim. The
circle clauses are stated on the piece subtype through `EdgeCirclePiece.proj`. -/
structure EdgeComponentsLink (P : EdgeBundle W) (M : EdgeComponentModels P) (H : EdgeLayer W)
    where
  handleEquiv : Fin H.handleCount ≃ Fin M.intervalCount
  circleEquiv : Fin H.edgeCircleCount ≃ Fin M.circleCount
  handle_whole : ∀ h,
    range (H.handle h).map = P.wholeComponent (M.componentEquiv (.inl (handleEquiv h)))
  circle_whole : ∀ j,
    range (H.edgeCircle j).piece.map =
      P.wholeComponent (M.componentEquiv (.inr (circleEquiv j)))
  handle_proj : ∀ h w t, ∃ hx : (H.handle h).map (w, t) ∈ P.source,
    P.proj ⟨(H.handle h).map (w, t), hx⟩ = M.intervalBase (handleEquiv h) t
  handle_disk : ∀ h t,
    range (fun w => (H.handle h).map (w, t)) = P.disk (M.intervalBase (handleEquiv h) t)
  handle_rim : ∀ h t,
    (fun w => (H.handle h).map (w, t)) '' diskRim = P.rim (M.intervalBase (handleEquiv h) t)
  circle_proj : ∀ j (q : (H.edgeCircle j).piece.Piece),
    ∃ hx : (H.edgeCircle j).piece.map q ∈ P.source,
      P.proj ⟨(H.edgeCircle j).piece.map q, hx⟩ =
        M.circleBase (circleEquiv j) ((H.edgeCircle j).proj q)
  circle_disk : ∀ j z,
    (H.edgeCircle j).piece.map '' {q | (H.edgeCircle j).proj q = z} =
      P.disk (M.circleBase (circleEquiv j) z)
  circle_rim : ∀ j z,
    (H.edgeCircle j).piece.map ''
        {q | (H.edgeCircle j).proj q = z ∧ (𝓡∂ 3).IsBoundaryPoint q} =
      P.rim (M.circleBase (circleEquiv j) z)

namespace EdgeComponentsLink

variable {P : EdgeBundle W} {M : EdgeComponentModels P} {H : EdgeLayer W}

/-- The endpoint of `C₂` at the end `b` of the handle `h`. -/
def endOfHandle (L : EdgeComponentsLink P M H) (h : Fin H.handleCount) (b : Bool) : P.EdgeEnd :=
  M.endpointEquiv (L.handleEquiv h, b)

/-- The base component of the handle `h`. -/
def componentOfHandle (L : EdgeComponentsLink P M H) (h : Fin H.handleCount) :
    P.EdgeBaseComponent :=
  M.componentEquiv (.inl (L.handleEquiv h))

/-- An end disk is the whole disk over the registered endpoint. -/
theorem endDisk_eq (L : EdgeComponentsLink P M H) (h : Fin H.handleCount) (b : Bool) :
    (H.handle h).endDisk b = P.disk (L.endOfHandle h b).1 := by
  rw [endOfHandle, M.endpointEquiv_apply]
  exact L.handle_disk h (iccEnd b)

theorem endOfHandle_injective (L : EdgeComponentsLink P M H) :
    Injective fun a : Fin H.handleCount × Bool => L.endOfHandle a.1 a.2 := by
  rintro ⟨h, b⟩ ⟨h', b'⟩ heq
  have h2 := M.endpointEquiv.injective heq
  simp only [Prod.mk.injEq] at h2
  exact Prod.ext (L.handleEquiv.injective h2.1) h2.2

/-- **§1.3, for S4 (derived).** Distinct handles have disjoint images: the component bijection
is injective and the images are the whole inverse images of distinct components. -/
theorem handle_ranges_disjoint_of_components (L : EdgeComponentsLink P M H) :
    Pairwise fun h h' =>
      Disjoint (range (H.handle h).map) (range (H.handle h').map) := by
  intro h h' hne
  rw [L.handle_whole h, L.handle_whole h']
  refine P.wholeComponent_disjoint fun heq => hne ?_
  exact L.handleEquiv.injective (Sum.inl_injective (M.componentEquiv.injective heq))

/-- **§1.3, for S9 (derived)**, including the two ends of one handle: the endpoint bijection
gives two distinct projection values, and a point has one projection value. -/
theorem endDisks_disjoint_of_components (L : EdgeComponentsLink P M H) :
    Pairwise fun a b : Fin H.handleCount × Bool =>
      Disjoint ((H.handle a.1).endDisk a.2) ((H.handle b.1).endDisk b.2) := by
  intro a b hne
  rw [L.endDisk_eq, L.endDisk_eq]
  refine P.disk_disjoint fun heq => hne ?_
  exact L.endOfHandle_injective (Subtype.ext heq)

/-- Distinct edge-circle pieces have disjoint images (derived, same component argument). -/
theorem edgeCircle_ranges_disjoint_of_components (L : EdgeComponentsLink P M H) :
    Pairwise fun j j' =>
      Disjoint (range (H.edgeCircle j).piece.map) (range (H.edgeCircle j').piece.map) := by
  intro j j' hne
  rw [L.circle_whole j, L.circle_whole j']
  refine P.wholeComponent_disjoint fun heq => hne ?_
  exact L.circleEquiv.injective (Sum.inr_injective (M.componentEquiv.injective heq))

/-- A handle and an edge-circle piece have disjoint images (derived). -/
theorem handle_edgeCircle_disjoint_of_components (L : EdgeComponentsLink P M H)
    (h : Fin H.handleCount) (j : Fin H.edgeCircleCount) :
    Disjoint (range (H.handle h).map) (range (H.edgeCircle j).piece.map) := by
  rw [L.handle_whole h, L.circle_whole j]
  refine P.wholeComponent_disjoint fun heq => ?_
  exact Sum.inl_ne_inr (M.componentEquiv.injective heq)

/-- Every base component is the component of a handle or of an edge-circle piece. -/
theorem exists_of_component (L : EdgeComponentsLink P M H) (C : P.EdgeBaseComponent) :
    (∃ h, M.componentEquiv (.inl (L.handleEquiv h)) = C) ∨
      ∃ j, M.componentEquiv (.inr (L.circleEquiv j)) = C := by
  rcases hs : M.componentEquiv.symm C with i | j
  · refine Or.inl ⟨L.handleEquiv.symm i, ?_⟩
    rw [Equiv.apply_symm_apply, ← hs, Equiv.apply_symm_apply]
  · refine Or.inr ⟨L.circleEquiv.symm j, ?_⟩
    rw [Equiv.apply_symm_apply, ← hs, Equiv.apply_symm_apply]

/-- The old union equation of `EdgeLink` (derived): handles and edge-circle pieces exhaust the
edge piece. -/
theorem iUnion_ranges_eq_edgePiece (L : EdgeComponentsLink P M H) :
    (⋃ h, range (H.handle h).map) ∪ (⋃ j, range (H.edgeCircle j).piece.map) =
      P.edgePiece := by
  apply Subset.antisymm
  · rintro x (hx | hx)
    · obtain ⟨h, hh⟩ := mem_iUnion.1 hx
      rw [L.handle_whole h] at hh
      obtain ⟨y, ⟨hy, hy'⟩, rfl⟩ := hh
      exact ⟨y, ⟨ActualComponent.subset _ hy, hy'⟩, rfl⟩
    · obtain ⟨j, hj⟩ := mem_iUnion.1 hx
      rw [L.circle_whole j] at hj
      obtain ⟨y, ⟨hy, hy'⟩, rfl⟩ := hj
      exact ⟨y, ⟨ActualComponent.subset _ hy, hy'⟩, rfl⟩
  · rintro _ ⟨y, ⟨hy, hy'⟩, rfl⟩
    have hC : P.proj y ∈ (ActualComponent.of hy).1 := mem_connectedComponentIn hy
    rcases L.exists_of_component (ActualComponent.of hy) with ⟨h, hh⟩ | ⟨j, hj⟩
    · refine Or.inl (mem_iUnion.2 ⟨h, ?_⟩)
      rw [L.handle_whole h, hh]
      exact ⟨y, ⟨hC, hy'⟩, rfl⟩
    · refine Or.inr (mem_iUnion.2 ⟨j, ?_⟩)
      rw [L.circle_whole j, hj]
      exact ⟨y, ⟨hC, hy'⟩, rfl⟩

end EdgeComponentsLink

end GC.GraphManifold.Assembly.FC39P0
