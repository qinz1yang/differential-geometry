import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCycleUnionPiece
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyBallHandleCycle
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1WSideRimProduct

/-!
# FC42 packet H3b: the `BallHandleCycle` of one cycle of the complete cycle partition

`CyclePartition.toBallHandleCycle j` fills every field of the corrected `BallHandleCycle` (with
`rim_quadrant`) for cycle `j` of a complete cycle partition (packet H2): balls `ballPiece`, the
oriented handles `cycleHandle` (reversed by the built `EdgeHandle.orient` where the cycle runs a
handle backwards), the certificate rim charts at the oriented ends `cycleRimChart`, the rounding
function `-ρ` (ρ = `circ.roundedFunction`; only the local `rim_pullback` uses it), the rim scales
of the corner charts, and the rounded union `roundedUnion j` of part 3. Incidence and disjointness
come from lane ASM-CYC2's H1 (`cycle_handle_ball_inter`, `cycle_ball_disjoint_of_hends`,
`cycle_handle_disjoint`), `rim_quadrant` from `DecompositionCertificate.rim_quadrant`.

Data consistency (review 42 §3.4) is definitional: `toBallHandleCycle_{len,ball,handle,rimChart,
roundingFn,union}` are `rfl`. Different cycles have disjoint rounded unions
(`pairwise_disjoint_unionSet`); a cycle and the rounded circle region are NOT disjoint (they meet
along `ρ = 0`), and no such statement is made. Every ball vertex and every handle lies in the
rounded union of its cycle. The rim-product clause of lane ASM-L1b (`D.RimProduct`) transfers to
every cycle (`rimProduct_toBallHandleCycle`, reversed handles by `RimProductAt.of_orient`), and the
balls lie in `W.interior` (`toBallHandleCycle_ball_subset_interior`, the `hint` input of L1).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance ballChartsC_ASMCYC3 : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

local instance ballSmoothC_ASMCYC3 : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 2

local instance diskChartsC_ASMCYC3 : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmoothC_ASMCYC3 : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

namespace DecompositionCertificate

namespace CyclePartition

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} {D : DecompositionCertificate W E}
  (P : D.CyclePartition)

/-- **H3b, the builder.** Every field of the corrected `BallHandleCycle` for cycle `j`, from the
certificate (rim data), the cycle partition (balls, oriented handles, `hends`), lane ASM-CYC2's H1
(incidence, disjointness) and H3a (the rounded union). -/
def toBallHandleCycle (j : Fin P.cnt) : BallHandleCycle W where
  len := P.len j
  len_pos := P.len_pos j
  ball := P.ballPiece j
  ballModel := P.ballModel j
  handle := P.cycleHandle j
  start_face k := P.cycleHandle_endDisk_subset j k false
  end_face k := P.cycleHandle_endDisk_subset j k true
  handle_ball_inter := cycle_handle_ball_inter D (P.len j) (P.ball j) (P.ball_injective j)
    (P.ballPiece j) (P.ballModel j) (P.vertex_ball j) (P.handle j) (P.orientation j)
    (P.handleEnd_handle j)
  ball_disjoint := cycle_ball_disjoint_of_hends D (P.len j) (P.ball j) (P.ball_injective j)
    (P.ballPiece j) (P.ballModel j) (P.vertex_ball j) (P.handle j) (P.orientation j)
    (P.handleEnd_handle j)
  handle_disjoint := cycle_handle_disjoint D (P.len j) (P.handle j) (P.handle_injective j)
    (P.orientation j)
  rimChart := P.cycleRimChart j
  rim_source k b := D.rim_source _ _
  rim_ball k b {p} hp := by
    have h := D.rim_vertex (P.handle j k) (xor b (P.orientation j k)) hp
    rwa [P.handleEnd_handle, ← P.range_ballPiece] at h
  rim_handle k b {p} hp := by
    rw [P.range_cycleHandle]
    exact D.rim_handle _ _ hp
  rim_quadrant k b p hp hx hy := by
    have h := D.rim_quadrant (P.ball j) (P.handle j) (P.handle j k) (xor b (P.orientation j k)) p
      hp hx hy
    have hR : (⋃ k', range (D.vertex (P.ball j k')).piece.map) = ⋃ k', range (P.ballPiece j k').map :=
      iUnion_congr fun k' => by rw [← Vertex.image_eq_range_piece, ← P.range_ballPiece]
    have hH : (⋃ k', range (P.cycleHandle j k').map) = ⋃ k', range (D.handle (P.handle j k')).map :=
      iUnion_congr fun k' => P.range_cycleHandle j k'
    change _ ∉ (⋃ k', range (P.ballPiece j k').map) ∪ ⋃ k', range (P.cycleHandle j k').map
    rw [hH, ← hR]
    exact h
  rim_label k b := by
    change D.rimChart _ _ '' _ = _
    rw [D.rim_label]
    congr 1
    funext x
    exact (EdgeHandle.orient_map_iccEnd (P.orientation j k) (D.handle (P.handle j k)) x b).symm
  rim_disjoint k b k' b' hne := by
    apply D.rim_disjoint
    intro heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨h1, h2⟩ := heq
    have hk := P.handle_injective j h1
    subst hk
    apply hne
    have : b = b' := by
      have h3 := congrArg (fun c => xor c (P.orientation j k)) h2
      simpa only [P.xor_xor_orientation] using h3
    rw [this]
  roundingFn x := -D.circ.roundedFunction x
  rimScale k b := D.circ.cornerScale (D.handleCorner (P.handle j k) (xor b (P.orientation j k)))
  rimScale_pos k b := D.circ.cornerScale_pos _
  rim_pullback k b p hp := by
    change -D.circ.roundedFunction (D.rimChart _ _ p) = _
    rw [D.roundedFunction_rimChart _ _ hp, neg_neg]
  union := P.roundedUnion j
  union_rim k b {p} hp := by
    rw [P.range_roundedUnion]
    exact P.mem_unionSet_rim_iff j k b hp
  union_away := by
    rw [P.range_roundedUnion]
    exact P.unionSet_diff_rimTargets j

theorem toBallHandleCycle_len (j : Fin P.cnt) : (P.toBallHandleCycle j).len = P.len j := rfl

theorem toBallHandleCycle_ball (j : Fin P.cnt) : (P.toBallHandleCycle j).ball = P.ballPiece j := rfl

theorem toBallHandleCycle_handle (j : Fin P.cnt) :
    (P.toBallHandleCycle j).handle = P.cycleHandle j := rfl

theorem toBallHandleCycle_rimChart (j : Fin P.cnt) :
    (P.toBallHandleCycle j).rimChart = P.cycleRimChart j := rfl

theorem toBallHandleCycle_roundingFn (j : Fin P.cnt) :
    (P.toBallHandleCycle j).roundingFn = fun x => -D.circ.roundedFunction x := rfl

theorem toBallHandleCycle_union (j : Fin P.cnt) :
    (P.toBallHandleCycle j).union = P.roundedUnion j := rfl

theorem range_toBallHandleCycle_union (j : Fin P.cnt) :
    range (P.toBallHandleCycle j).union.map = P.unionSet j :=
  P.range_roundedUnion j

theorem unionSet_subset_coreSet_union_rimTargets (j : Fin P.cnt) :
    P.unionSet j ⊆ P.coreSet j ∪ P.rimTargets j := by
  rintro x (hx | hx)
  · exact Or.inl hx
  · exact Or.inr (P.fillet_subset_rimTargets j hx)

theorem disjoint_coreSet (j j' : Fin P.cnt) (hjj : j ≠ j') :
    Disjoint (P.coreSet j) (P.coreSet j') := by
  have hball : ∀ k k', P.ball j k ≠ P.ball j' k' := fun k k' h =>
    hjj (congrArg Sigma.fst (P.ball_eq_ball_iff.mp h))
  have hhandle : ∀ k k', P.handle j k ≠ P.handle j' k' := fun k k' h =>
    hjj (congrArg Sigma.fst (P.handle_eq_handle_iff.mp h))
  -- handle of one cycle versus ball of the other
  have hHB : ∀ (j₁ j₂ : Fin P.cnt), j₁ ≠ j₂ → ∀ k₁ k₂,
      Disjoint (range (D.handle (P.handle j₁ k₁)).map) (D.vertex (P.ball j₂ k₂)).image := by
    intro j₁ j₂ hj k₁ k₂
    rw [Set.disjoint_iff]
    intro x hx
    have hmem := (D.handle_inter_vertex_image (P.handle j₁ k₁) (P.ball j₂ k₂)).subset hx
    obtain ⟨b, hb⟩ := mem_iUnion.mp hmem
    obtain ⟨hbv, -⟩ := mem_iUnion.mp hb
    rw [P.handleEnd_handle_eq] at hbv
    exact hj (congrArg Sigma.fst (P.ball_eq_ball_iff.mp hbv))
  rw [Set.disjoint_left]
  rintro x (hx | hx) (hx' | hx')
  · obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    obtain ⟨k', hk'⟩ := mem_iUnion.mp hx'
    exact Set.disjoint_left.mp (D.ball_image_disjoint_vertex_image (P.ball_isBall j k)
      (P.exists_partitioned_face j k) (hball k k')) (P.ball_mem_vertex_image hk)
      (P.ball_mem_vertex_image hk')
  · obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    obtain ⟨k', hk'⟩ := mem_iUnion.mp hx'
    rw [P.range_cycleHandle] at hk'
    exact Set.disjoint_left.mp (hHB j' j (Ne.symm hjj) k' k) hk' (P.ball_mem_vertex_image hk)
  · obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    obtain ⟨k', hk'⟩ := mem_iUnion.mp hx'
    rw [P.range_cycleHandle] at hk
    exact Set.disjoint_left.mp (hHB j j' hjj k k') hk (P.ball_mem_vertex_image hk')
  · obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    obtain ⟨k', hk'⟩ := mem_iUnion.mp hx'
    rw [P.range_cycleHandle] at hk hk'
    exact Set.disjoint_left.mp (D.handle_images_disjoint (hhandle k k')) hk hk'

theorem disjoint_rimTargets_coreSet (j j' : Fin P.cnt) (hjj : j ≠ j') :
    Disjoint (P.rimTargets j) (P.coreSet j') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  obtain ⟨k, b, hxT⟩ := mem_iUnion₂.mp hx
  rcases hx' with hB | hH
  · obtain ⟨k', hk'⟩ := mem_iUnion.mp hB
    have hne : P.ball j' k' ≠ D.handleEnd (P.handle j k) (xor b (P.orientation j k)) := by
      rw [P.handleEnd_handle]
      intro h
      exact hjj (congrArg Sigma.fst (P.ball_eq_ball_iff.mp h)).symm
    exact Set.disjoint_left.mp (D.disjoint_vertex_rimChart_target _ _ _ hne)
      (P.ball_mem_vertex_image hk') hxT
  · obtain ⟨k', hk'⟩ := mem_iUnion.mp hH
    rw [P.range_cycleHandle] at hk'
    have hne : P.handle j' k' ≠ P.handle j k := fun h =>
      hjj (congrArg Sigma.fst (P.handle_eq_handle_iff.mp h)).symm
    exact Set.disjoint_left.mp (D.disjoint_handle_rimChart_target _ _ _ hne) hk' hxT

theorem disjoint_rimTargets (j j' : Fin P.cnt) (hjj : j ≠ j') :
    Disjoint (P.rimTargets j) (P.rimTargets j') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  obtain ⟨k, b, hxT⟩ := mem_iUnion₂.mp hx
  obtain ⟨k', b', hxT'⟩ := mem_iUnion₂.mp hx'
  have hne : (P.handle j k, xor b (P.orientation j k)) ≠
      (P.handle j' k', xor b' (P.orientation j' k')) := fun h =>
    hjj (congrArg Sigma.fst (P.handle_eq_handle_iff.mp (congrArg Prod.fst h)))
  exact Set.disjoint_left.mp (D.rim_disjoint _ _ _ _ hne) hxT hxT'

/-- **Different cycles have disjoint rounded unions.** (A cycle and the rounded circle region are
NOT disjoint: they meet along the zero level of `ρ`.) -/
theorem pairwise_disjoint_unionSet : Pairwise fun j j' => Disjoint (P.unionSet j) (P.unionSet j') := by
  intro j j' hjj
  refine Disjoint.mono (P.unionSet_subset_coreSet_union_rimTargets j)
    (P.unionSet_subset_coreSet_union_rimTargets j') ?_
  refine Disjoint.union_left (Disjoint.union_right (P.disjoint_coreSet j j' hjj) ?_)
    (Disjoint.union_right (P.disjoint_rimTargets_coreSet j j' hjj) (P.disjoint_rimTargets j j' hjj))
  exact (P.disjoint_rimTargets_coreSet j' j (Ne.symm hjj)).symm

/-- Cover: every ball vertex lies in the rounded union of its cycle. -/
theorem vertex_image_subset_unionSet (k : Fin D.vertexCount) (hk : (D.vertex k).IsBall) :
    (D.vertex k).image ⊆ P.unionSet (P.ballIdx.symm ⟨k, hk⟩).1 := by
  have h := P.ball_ballIdx_symm k hk
  intro x hx
  apply P.coreSet_subset_unionSet
  apply P.ball_subset_coreSet _ (P.ballIdx.symm ⟨k, hk⟩).2
  rw [h]
  exact hx

/-- Cover: every handle lies in the rounded union of its cycle. -/
theorem handle_range_subset_unionSet (h : Fin D.handleCount) :
    range (D.handle h).map ⊆ P.unionSet (P.handleIdx.symm h).1 := by
  have h1 := P.handle_handleIdx_symm h
  intro x hx
  apply P.coreSet_subset_unionSet
  apply P.handle_subset_coreSet _ (P.handleIdx.symm h).2
  rw [h1]
  exact hx

/-- **Transport of the rim-product clause** from the certificate (`D.RimProduct`, every rim chart
a product in its handle's own coordinates) to the cycle builder: reversed handles are covered by
`RimProductAt.of_orient` (`t ↦ 1 − t` exchanges the two ends). -/
theorem rimProduct_toBallHandleCycle (hprodD : D.RimProduct) (j : Fin P.cnt) :
    (P.toBallHandleCycle j).RimProduct := by
  intro k b
  change RimProductAt (D.rimChart (P.handle j k) (xor b (P.orientation j k)))
    ((D.handle (P.handle j k)).orient (P.orientation j k)) b
  refine RimProductAt.of_orient (P.orientation j k) b (fun h => by rw [h]; rfl)
    (fun h w t t' ht => ?_) (hprodD _ _)
  rw [h]
  change (D.handle (P.handle j k)).reverse.map (w, t) = _
  rw [EdgeHandle.reverse_map]
  congr 2
  ext
  rw [iccReflect_val, ht]

/-- The balls of the cycle lie in the interior of `W` (the `hint` input of lane ASM-L1b's L1). -/
theorem toBallHandleCycle_ball_subset_interior (j : Fin P.cnt) (k : Fin (P.toBallHandleCycle j).len) :
    range ((P.toBallHandleCycle j).ball k).map ⊆ (W.interior : Set W.Carrier) := fun _ hx =>
  P.unionSet_subset_interior j (P.coreSet_subset_unionSet j (Or.inl (mem_iUnion.mpr ⟨k, hx⟩)))

end CyclePartition

end DecompositionCertificate

end GC.GraphManifold.Assembly
