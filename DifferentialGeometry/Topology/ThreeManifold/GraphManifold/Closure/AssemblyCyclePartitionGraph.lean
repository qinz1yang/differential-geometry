import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCyclePartitionBallFace
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyFC42Models
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyRimRounding
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.DegreeTwoMultigraph

/-!
# FC42 packet H2-b: the complete cycle partition of the ball–handle multigraph

Review 40 §3.5 (disposition B7 (c)): the cycles of FC42 step 6 must come with index EQUIVALENCES,
not only "each cycle ball is a ball, each handle is used". `DecompositionCertificate.CyclePartition D`
records `cnt` cycles of lengths `len j > 0`, the equivalences
`(Σ j, Fin (len j)) ≃ {k // (D.vertex k).IsBall}` and `(Σ j, Fin (len j)) ≃ Fin D.handleCount`, a
traversal orientation `orient`, and the builder identity of `dry_cycleOfCertificate`
`D.handleEnd (handleIdx ⟨j, k⟩) (xor b (orient ⟨j, k⟩)) = ballIdx ⟨j, rimBall (len j) k b⟩`.

**Producer** `nonempty_cyclePartition`: without sphere seams and with every partitioned sphere face
owned by a ball (`hball`; lane ASM-CYC2's `badVertexCount D = 0`), the multigraph with vertices the
ball vertices, edges the handles and ends `handleEnd h false`, `handleEnd h true` (all ball vertices:
`isBall_handleEnd`) has degree two at every vertex (`card_handleEnd_eq_two_of_isBall`, FC40), so the
built `exists_cycle_decomposition_of_degree_two` applies; the unordered edge ends are ordered by
`orient` (handles traversed backwards are reversed by the built `EdgeHandle.orient`).

The per-cycle builder data (`CyclePartition.ball`, `.handle`, `.ballPiece`, `.ballModel`,
`.cycleHandle`, injectivity, `handleEnd_handle`, the partitioned face of each ball) are the inputs of
the `BallHandleCycle` builder (packet H3b).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance ballChartsG_ASMCYC3 : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

local instance ballSmoothG_ASMCYC3 : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 2

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)

/-- **The complete cycle partition** of the ball–handle multigraph (review 40 §3.5): `cnt` cycles of
lengths `len j > 0`, index EQUIVALENCES with the ball vertices and with all handles, a traversal
orientation, and the builder identity `handleEnd_eq`. -/
structure CyclePartition where
  cnt : ℕ
  len : Fin cnt → ℕ
  len_pos : ∀ j, 0 < len j
  ballIdx : (Σ j, Fin (len j)) ≃ {k : Fin D.vertexCount // (D.vertex k).IsBall}
  handleIdx : (Σ j, Fin (len j)) ≃ Fin D.handleCount
  orient : (Σ j, Fin (len j)) → Bool
  handleEnd_eq : ∀ j k b, D.handleEnd (handleIdx ⟨j, k⟩) (xor b (orient ⟨j, k⟩)) =
    (ballIdx ⟨j, rimBall (len j) k b⟩ : Fin D.vertexCount)

/-- The dart count of the handle ends at a vertex: source ends plus target ends. -/
theorem card_handleEnd_false_add_card_handleEnd_true (k : Fin D.vertexCount) :
    (Finset.univ.filter fun h : Fin D.handleCount => D.handleEnd h false = k).card +
        (Finset.univ.filter fun h : Fin D.handleCount => D.handleEnd h true = k).card =
      (Finset.univ.filter fun hb : Fin D.handleCount × Bool => D.handleEnd hb.1 hb.2 = k).card := by
  rw [← DegreeTwoMultigraph.card_dartHead_eq (fun h => D.handleEnd h false)
    (fun h => D.handleEnd h true) k]
  congr 1
  refine Finset.filter_congr fun hb _ => ?_
  obtain ⟨h, b⟩ := hb
  cases b <;> exact Iff.rfl

/-- **Degree two** of the ball–handle multigraph, in the form of
`exists_cycle_decomposition_of_degree_two`. -/
theorem card_src_add_card_tgt_eq_two (hsph : D.sphereSeamCount = 0)
    (hball : ∀ f, D.faceKind f = .partitioned →
      (∃ e : D.face f ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, D.faceModel f = .inl e) →
      (D.vertex (D.faceOwner f)).IsBall)
    (w : {k : Fin D.vertexCount // (D.vertex k).IsBall}) :
    (Finset.univ.filter fun h : Fin D.handleCount =>
        (⟨D.handleEnd h false, D.isBall_handleEnd hball h false⟩ :
          {k : Fin D.vertexCount // (D.vertex k).IsBall}) = w).card +
      (Finset.univ.filter fun h : Fin D.handleCount =>
        (⟨D.handleEnd h true, D.isBall_handleEnd hball h true⟩ :
          {k : Fin D.vertexCount // (D.vertex k).IsBall}) = w).card = 2 := by
  have h1 : ∀ b : Bool, (Finset.univ.filter fun h : Fin D.handleCount =>
      (⟨D.handleEnd h b, D.isBall_handleEnd hball h b⟩ :
        {k : Fin D.vertexCount // (D.vertex k).IsBall}) = w) =
      Finset.univ.filter fun h : Fin D.handleCount => D.handleEnd h b = w.1 := fun b => by
    ext h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Subtype.ext_iff]
  rw [h1, h1, D.card_handleEnd_false_add_card_handleEnd_true]
  exact D.card_handleEnd_eq_two_of_isBall hsph w.2

/-- **H2 (producer).** Without sphere seams and with every partitioned sphere face owned by a ball
(`hball`, i.e. `badVertexCount D = 0`), the certificate has a complete cycle partition. -/
theorem nonempty_cyclePartition (hsph : D.sphereSeamCount = 0)
    (hball : ∀ f, D.faceKind f = .partitioned →
      (∃ e : D.face f ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, D.faceModel f = .inl e) →
      (D.vertex (D.faceOwner f)).IsBall) :
    Nonempty D.CyclePartition := by
  let V := {k : Fin D.vertexCount // (D.vertex k).IsBall}
  let src : Fin D.handleCount → V := fun h => ⟨D.handleEnd h false, D.isBall_handleEnd hball h false⟩
  let tgt : Fin D.handleCount → V := fun h => ⟨D.handleEnd h true, D.isBall_handleEnd hball h true⟩
  obtain ⟨C, nC, hfin, hpos, vtx, edg, hcyc⟩ :=
    exists_cycle_decomposition_of_degree_two src tgt (D.card_src_add_card_tgt_eq_two hsph hball)
  let eC : Fin (Nat.card C) ≃ C := (Finite.equivFin C).symm
  let σC : (Σ j : Fin (Nat.card C), Fin (nC (eC j))) ≃ Σ c : C, Fin (nC c) :=
    Equiv.sigmaCongrLeft (β := fun c => Fin (nC c)) eC
  refine ⟨{
    cnt := Nat.card C
    len := fun j => nC (eC j)
    len_pos := fun j => hpos _
    ballIdx := σC.trans vtx
    handleIdx := σC.trans edg
    orient := fun p => !decide (src (edg (σC p)) = vtx (σC p) ∧
      tgt (edg (σC p)) = vtx ⟨(σC p).1, finRotate _ (σC p).2⟩)
    handleEnd_eq := ?_ }⟩
  intro j k b
  have hk := Sym2.eq_iff.mp (hcyc (eC j) k)
  change D.handleEnd (edg ⟨eC j, k⟩) (xor b (!decide (src (edg ⟨eC j, k⟩) = vtx ⟨eC j, k⟩ ∧
      tgt (edg ⟨eC j, k⟩) = vtx ⟨eC j, finRotate _ k⟩))) = (vtx ⟨eC j, rimBall _ k b⟩).1
  by_cases hc : src (edg ⟨eC j, k⟩) = vtx ⟨eC j, k⟩ ∧
      tgt (edg ⟨eC j, k⟩) = vtx ⟨eC j, finRotate _ k⟩
  · rw [decide_eq_true hc]
    cases b
    · exact congrArg Subtype.val hc.1
    · exact congrArg Subtype.val hc.2
  · rw [decide_eq_false hc]
    have hc' := hk.resolve_left hc
    cases b
    · exact congrArg Subtype.val hc'.2
    · exact congrArg Subtype.val hc'.1

namespace CyclePartition

variable {D} (P : D.CyclePartition)

/-- The ball vertex at position `k` of cycle `j`. -/
def ball (j : Fin P.cnt) (k : Fin (P.len j)) : Fin D.vertexCount :=
  (P.ballIdx ⟨j, k⟩).1

theorem ball_isBall (j : Fin P.cnt) (k : Fin (P.len j)) : (D.vertex (P.ball j k)).IsBall :=
  (P.ballIdx ⟨j, k⟩).2

theorem ball_injective (j : Fin P.cnt) : Injective (P.ball j) := fun k k' h => by
  have h1 : P.ballIdx ⟨j, k⟩ = P.ballIdx ⟨j, k'⟩ := Subtype.ext h
  exact eq_of_heq (Sigma.mk.inj_iff.mp (P.ballIdx.injective h1)).2

/-- The handle (certificate index) at position `k` of cycle `j`. -/
def handle (j : Fin P.cnt) (k : Fin (P.len j)) : Fin D.handleCount :=
  P.handleIdx ⟨j, k⟩

theorem handle_injective (j : Fin P.cnt) : Injective (P.handle j) := fun _ _ h =>
  eq_of_heq (Sigma.mk.inj_iff.mp (P.handleIdx.injective h)).2

/-- The traversal orientation of cycle `j`. -/
def orientation (j : Fin P.cnt) (k : Fin (P.len j)) : Bool :=
  P.orient ⟨j, k⟩

/-- The builder identity `hends` of `dry_cycleOfCertificate`, per cycle. -/
theorem handleEnd_handle (j : Fin P.cnt) (k : Fin (P.len j)) (b : Bool) :
    D.handleEnd (P.handle j k) (xor b (P.orientation j k)) = P.ball j (rimBall (P.len j) k b) :=
  P.handleEnd_eq j k b

/-- The piece of the ball at position `k` of cycle `j`. -/
def ballPiece (j : Fin P.cnt) (k : Fin (P.len j)) : PieceEmbedding W :=
  (P.ball_isBall j k).piece

/-- Its ball model. -/
def ballModel (j : Fin P.cnt) (k : Fin (P.len j)) :
    (P.ballPiece j k).Piece ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3 :=
  (P.ball_isBall j k).model

theorem vertex_ball (j : Fin P.cnt) (k : Fin (P.len j)) :
    D.vertex (P.ball j k) = .zero (P.ballPiece j k) (.ball (P.ballModel j k)) :=
  (P.ball_isBall j k).eq

/-- The handle at position `k` of cycle `j`, run in the traversal direction. -/
def cycleHandle (j : Fin P.cnt) (k : Fin (P.len j)) : EdgeHandle W :=
  (D.handle (P.handle j k)).orient (P.orientation j k)

/-- Each ball of a cycle owns a partitioned face (the face of its outgoing handle end): the
`hpart` input of lane ASM-CYC2's disjointness statements. -/
theorem exists_partitioned_face (j : Fin P.cnt) (k : Fin (P.len j)) :
    ∃ f, D.faceOwner f = P.ball j k ∧ D.faceKind f = .partitioned :=
  ⟨D.handleFace (P.handle j k) (xor false (P.orientation j k)),
    (D.handleFace_owner _ _).trans (P.handleEnd_handle j k false),
    D.handleFace_kind _ _⟩

/-- Every ball vertex is a ball of a cycle. -/
theorem ball_ballIdx_symm (k : Fin D.vertexCount) (hk : (D.vertex k).IsBall) :
    P.ball (P.ballIdx.symm ⟨k, hk⟩).1 (P.ballIdx.symm ⟨k, hk⟩).2 = k := by
  change (P.ballIdx ⟨(P.ballIdx.symm ⟨k, hk⟩).1, (P.ballIdx.symm ⟨k, hk⟩).2⟩).1 = k
  rw [Sigma.eta, Equiv.apply_symm_apply]

/-- Every handle is a handle of a cycle. -/
theorem handle_handleIdx_symm (h : Fin D.handleCount) :
    P.handle (P.handleIdx.symm h).1 (P.handleIdx.symm h).2 = h := by
  change P.handleIdx ⟨(P.handleIdx.symm h).1, (P.handleIdx.symm h).2⟩ = h
  rw [Sigma.eta, Equiv.apply_symm_apply]

variable {P} in
/-- Balls of different positions (in any cycles) are different vertices. -/
theorem ball_eq_ball_iff {j j' : Fin P.cnt} {k : Fin (P.len j)} {k' : Fin (P.len j')} :
    P.ball j k = P.ball j' k' ↔ (⟨j, k⟩ : Σ j, Fin (P.len j)) = ⟨j', k'⟩ := by
  constructor
  · intro h
    exact P.ballIdx.injective (Subtype.ext h)
  · intro h
    rw [Sigma.mk.inj_iff] at h
    obtain ⟨rfl, h⟩ := h
    rw [eq_of_heq h]

variable {P} in
/-- Handles of different positions (in any cycles) are different handles. -/
theorem handle_eq_handle_iff {j j' : Fin P.cnt} {k : Fin (P.len j)} {k' : Fin (P.len j')} :
    P.handle j k = P.handle j' k' ↔ (⟨j, k⟩ : Σ j, Fin (P.len j)) = ⟨j', k'⟩ := by
  constructor
  · intro h
    exact P.handleIdx.injective h
  · intro h
    rw [Sigma.mk.inj_iff] at h
    obtain ⟨rfl, h⟩ := h
    rw [eq_of_heq h]

end CyclePartition

end DecompositionCertificate

end GC.GraphManifold.Assembly
