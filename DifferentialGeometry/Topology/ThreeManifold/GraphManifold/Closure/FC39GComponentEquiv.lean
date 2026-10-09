import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Edges

/-!
# FC39 GROUP G, target `stub_totalComponentEquiv` (lane FC39-G1)

The frozen target `T:283–286` (`docs/geometrization/chapter14/evidence/fc39-p0/Targets.lean.txt`),
proved as a general theorem on the contract (external review 56, D56-1): the finite labels of an
`EdgeComponentModels P` are in bijection with the ACTUAL connected components of the edge piece,
the label `s` going to the whole inverse image of its base component `M.componentEquiv s`.

Route (not a count):

* `EdgeBundle.connectedComponentIn_edgePiece_subset_G1` — a connected subset of the edge piece
  through a point over the base component `C` stays over `C`: its preimage in the source is
  preconnected (the source inclusion is inducing), so is its projection, which then lies in the
  actual component `C` of `C₂` (`IsPreconnected.subset_connectedComponentIn`);
* `EdgeComponentModels.wholeComponent_isPreconnected_G1` — the whole inverse image is the range of
  the model `D² × [0, 1]` (resp. `D² × S¹`), a continuous image of a connected space;
* hence `connectedComponentIn_edgePiece_eq_G1`: the actual component through a point of a whole
  component IS that whole component; injectivity from the disjointness of whole components and
  their non-emptiness, surjectivity from the base component of a point of the edge piece.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

local instance diskCharts_G1 : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

variable {W : CompactCarrier.{u}}

namespace EdgeBundle

variable (P : EdgeBundle W)

/-- A whole component lies in the edge piece. -/
theorem wholeComponent_subset_edgePiece_G1 (C : P.EdgeBaseComponent) :
    P.wholeComponent C ⊆ P.edgePiece := by
  rintro _ ⟨y, ⟨hy, hy'⟩, rfl⟩
  exact ⟨y, ⟨C.subset hy, hy'⟩, rfl⟩

/-- A point of the edge piece lies in the whole component of the actual base component through
its projection. -/
theorem mem_wholeComponent_of_G1 {y : P.source} (hy : P.proj y ∈ P.cbase)
    (hl : P.height y ≤ P.level) :
    (y : W.Carrier) ∈ P.wholeComponent (ActualComponent.of hy) :=
  ⟨y, ⟨mem_connectedComponentIn hy, hl⟩, rfl⟩

/-- **The actual component of the edge piece through a point of a whole component stays in it**:
the preimage of the component in the source is preconnected, so is its projection, which lies in
`C₂` and meets the actual base component `C`. -/
theorem connectedComponentIn_edgePiece_subset_G1 {C : P.EdgeBaseComponent} {x : W.Carrier}
    (hx : x ∈ P.wholeComponent C) :
    connectedComponentIn P.edgePiece x ⊆ P.wholeComponent C := by
  obtain ⟨y, ⟨hyC, hyl⟩, rfl⟩ := hx
  have hyE : (y : W.Carrier) ∈ P.edgePiece := ⟨y, ⟨C.subset hyC, hyl⟩, rfl⟩
  -- the preimage of the component in the source
  have himage : Subtype.val '' (Subtype.val ⁻¹' connectedComponentIn P.edgePiece (y : W.Carrier) :
      Set P.source) = connectedComponentIn P.edgePiece (y : W.Carrier) := by
    apply Subset.antisymm (image_preimage_subset _ _)
    intro z hz
    obtain ⟨w, -, rfl⟩ := connectedComponentIn_subset _ _ hz
    exact ⟨w, hz, rfl⟩
  have hpre : IsPreconnected (Subtype.val ⁻¹' connectedComponentIn P.edgePiece (y : W.Carrier) :
      Set P.source) := by
    have hind : Topology.IsInducing (Subtype.val : P.source → W.Carrier) :=
      Topology.IsInducing.subtypeVal
    rw [← hind.isPreconnected_image, himage]
    exact isPreconnected_connectedComponentIn
  -- every point of the preimage lies below the level over `C₂`
  have hbelow : ∀ w : P.source, (w : W.Carrier) ∈ connectedComponentIn P.edgePiece
      (y : W.Carrier) → P.proj w ∈ P.cbase ∧ P.height w ≤ P.level := by
    intro w hw
    obtain ⟨w', hw', hww'⟩ := connectedComponentIn_subset _ _ hw
    obtain rfl : w' = w := Subtype.ext hww'
    exact hw'
  -- the projection lies in the actual base component through `proj y`
  have hproj : P.proj '' (Subtype.val ⁻¹' connectedComponentIn P.edgePiece (y : W.Carrier) :
      Set P.source) ⊆ connectedComponentIn P.cbase (P.proj y) := by
    refine (hpre.image _ P.proj.continuous.continuousOn).subset_connectedComponentIn
      ⟨y, mem_connectedComponentIn hyE, rfl⟩ ?_
    rintro _ ⟨w, hw, rfl⟩
    exact (hbelow w hw).1
  have hC : connectedComponentIn P.cbase (P.proj y) = C.1 := by
    obtain ⟨c, -, hc⟩ := C.2
    rw [hc] at hyC ⊢
    exact (connectedComponentIn_eq hyC).symm
  intro z hz
  obtain ⟨w, hw, rfl⟩ := connectedComponentIn_subset _ _ hz
  refine ⟨w, ⟨?_, (hbelow w hz).2⟩, rfl⟩
  rw [← hC]
  exact hproj ⟨w, hz, rfl⟩

/-- **A preconnected whole component is the actual component of the edge piece through each of its
points.** -/
theorem connectedComponentIn_edgePiece_eq_G1 {C : P.EdgeBaseComponent} {x : W.Carrier}
    (hx : x ∈ P.wholeComponent C) (hC : IsPreconnected (P.wholeComponent C)) :
    connectedComponentIn P.edgePiece x = P.wholeComponent C :=
  Subset.antisymm (P.connectedComponentIn_edgePiece_subset_G1 hx)
    (hC.subset_connectedComponentIn hx (P.wholeComponent_subset_edgePiece_G1 C))

end EdgeBundle

namespace EdgeComponentModels

variable {P : EdgeBundle W} (M : EdgeComponentModels P)

/-- The closed disk `D²` is preconnected (convex). -/
theorem closedCell_two_preconnectedSpace_G1 : PreconnectedSpace (ClosedCell 2) := by
  have hconv : Convex ℝ ({x : EuclideanSpace ℝ (Fin 2) | ‖x‖ ≤ 1} : Set _) := by
    simpa only [Metric.closedBall, dist_zero_right] using
      (convex_closedBall (0 : EuclideanSpace ℝ (Fin 2)) (1 : ℝ))
  exact Subtype.preconnectedSpace hconv.isPreconnected

/-- **Every whole component is preconnected**: it is the range of its model `D² × [0, 1]`
(resp. `D² × S¹`). -/
theorem wholeComponent_isPreconnected_G1 (s : Fin M.intervalCount ⊕ Fin M.circleCount) :
    IsPreconnected (P.wholeComponent (M.componentEquiv s)) := by
  rcases s with i | j
  · rw [← M.intervalTriv_range i]
    have : PreconnectedSpace (ClosedCell 2) := closedCell_two_preconnectedSpace_G1
    have : PreconnectedSpace (Icc (0 : ℝ) 1) :=
      Subtype.preconnectedSpace isPreconnected_Icc
    exact isPreconnected_range (M.intervalTriv i).smooth.continuous
  · rw [← M.circleTriv_range j]
    have : PreconnectedSpace (ClosedCell 2) := closedCell_two_preconnectedSpace_G1
    exact isPreconnected_range (M.circleTriv_smooth j).continuous

/-- **Every whole component is non-empty** (the range of its model). -/
theorem wholeComponent_nonempty_G1 (s : Fin M.intervalCount ⊕ Fin M.circleCount) :
    (P.wholeComponent (M.componentEquiv s)).Nonempty := by
  rcases s with i | j
  · rw [← M.intervalTriv_range i]
    exact ⟨_, (closedCellCenter 2, ⟨0, left_mem_Icc.2 zero_le_one⟩), rfl⟩
  · rw [← M.circleTriv_range j]
    exact ⟨_, (closedCellCenter 2, 1), rfl⟩

/-- The actual component of the edge piece of the label `s`: the whole inverse image of its base
component. -/
def actualComponent_G1 (s : Fin M.intervalCount ⊕ Fin M.circleCount) : P.EdgeActualComponent :=
  ⟨P.wholeComponent (M.componentEquiv s), (M.wholeComponent_nonempty_G1 s).some,
    P.wholeComponent_subset_edgePiece_G1 _ (M.wholeComponent_nonempty_G1 s).some_mem,
    (P.connectedComponentIn_edgePiece_eq_G1 (M.wholeComponent_nonempty_G1 s).some_mem
      (M.wholeComponent_isPreconnected_G1 s)).symm⟩

theorem actualComponent_G1_val (s : Fin M.intervalCount ⊕ Fin M.circleCount) :
    (M.actualComponent_G1 s).1 = P.wholeComponent (M.componentEquiv s) :=
  rfl

/-- Distinct labels give distinct actual components (whole components of distinct base components
are disjoint and non-empty). -/
theorem actualComponent_G1_injective : Injective M.actualComponent_G1 := by
  intro s s' hss'
  have hval : P.wholeComponent (M.componentEquiv s) = P.wholeComponent (M.componentEquiv s') :=
    congrArg Subtype.val hss'
  by_contra hne
  have hdisj := P.wholeComponent_disjoint fun h => hne (M.componentEquiv.injective h)
  rw [hval] at hdisj
  obtain ⟨x, hx⟩ := M.wholeComponent_nonempty_G1 s'
  exact Set.disjoint_left.1 hdisj hx hx

/-- Every actual component of the edge piece is the whole component of a label. -/
theorem actualComponent_G1_surjective : Surjective M.actualComponent_G1 := by
  rintro ⟨K, x, hx, rfl⟩
  obtain ⟨y, ⟨hy, hl⟩, rfl⟩ := hx
  refine ⟨M.componentEquiv.symm (ActualComponent.of hy), Subtype.ext ?_⟩
  have hmem : (y : W.Carrier) ∈ P.wholeComponent
      (M.componentEquiv (M.componentEquiv.symm (ActualComponent.of hy))) := by
    rw [Equiv.apply_symm_apply]
    exact P.mem_wholeComponent_of_G1 hy hl
  exact (P.connectedComponentIn_edgePiece_eq_G1 hmem (M.wholeComponent_isPreconnected_G1 _)).symm

/-- The bijection of the labels with the actual components of the edge piece. -/
def totalComponentEquivOf_G1 :
    (Fin M.intervalCount ⊕ Fin M.circleCount) ≃ P.EdgeActualComponent :=
  Equiv.ofBijective M.actualComponent_G1
    ⟨M.actualComponent_G1_injective, M.actualComponent_G1_surjective⟩

end EdgeComponentModels

/-- **GROUP G, `stub_totalComponentEquiv` (frozen statement `T:283–286`).** The finite labels are
in bijection with the actual components of the edge piece, each component being the whole inverse
image of its base component. -/
theorem totalComponentEquiv_G1 (P : EdgeBundle W) (M : EdgeComponentModels P) :
    ∃ e : (Fin M.intervalCount ⊕ Fin M.circleCount) ≃ P.EdgeActualComponent,
      ∀ s, (e s).1 = P.wholeComponent (M.componentEquiv s) :=
  ⟨M.totalComponentEquivOf_G1, fun _ => rfl⟩

end GC.GraphManifold.Assembly.FC39P0
