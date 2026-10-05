import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereRecCellChart
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereRecSides
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutShellChart
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutBallRelocationApplications
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCyclePartitionBallFace
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyFC42ClosedPieces

/-!
# FC42 sphere recursion, packet S3a: a ball side and its cap make a three-sphere

Lane ASM-SPH (review 40 §2.1 table, §2.4 "second layer"). For the cut-and-capped data
`X : SphereCutCapped W S E` and a piece `P` of `W` on side `j` of the seam whose whole half collar
of side `j` lies in it and whose model boundary is exactly the seam sphere (a ball side vertex):

* `range_liftPiece_inter_cap`: the lifted piece meets the cap of its copy exactly in the cut sphere;
* `isOpen_capUnion`: the union `lift ∪ cap` is open (near the cut sphere it contains the shell ball
  chart of the cap, `RelativeSphereCapping.exists_shellBallChart`), and compact;
* `nonempty_capUnion_sphereDiffeomorph`: for a ball side (`P ≅ D³`) the union is diffeomorphic to the
  round `S³` — for the ACTUAL attaching map of the capping: two full-rank cells cover it
  (`nonempty_sphereDiffeomorph_of_closedCell_cover`), whatever the gluing.

Certificate level (`DecompositionCertificate`): for a sphere seam `c` whose side `b` is a ball
(`Vertex.IsBall`, lane ASM-CYC3), the lifted side vertex and the cap of its copy make an open set of
the capped carrier diffeomorphic to `S³` (`capUnion_ball_sphere`); it is the whole component of the
capped carrier containing that cap (`capUnion_eq_componentPiece`), so that component is `S³`
(`componentCarrier_sphere_of_ball`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance ballChartsCapBall_ASMSPH : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

local instance ballSmoothCapBall_ASMSPH : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 2

local instance sphereDimFourCapBall_ASMSPH :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) :=
  ⟨by simp⟩

/-- A piece whose model boundary is the seam sphere lies in `W.interior`. -/
theorem range_subset_interior_of_boundary_eq_zeroSphere {W : CompactCarrier.{u}}
    {S : SphereSeam W} (P : PieceEmbedding W)
    (hbd : P.map '' (𝓡∂ 3).boundary P.Piece = S.zeroSphere) : range P.map ⊆ W.interior := by
  rintro _ ⟨q, rfl⟩
  rcases (𝓡∂ 3).isInteriorPoint_or_isBoundaryPoint q with hq | hq
  · exact P.isInteriorPoint_map hq
  · have hx : P.map q ∈ S.zeroSphere := hbd ▸ ⟨q, hq, rfl⟩
    exact S.target_interior (S.zeroSphere_subset_target hx)

namespace SphereCutCapped

variable {W : CompactCarrier.{u}} {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n}
  (X : SphereCutCapped W S E)

/-- The core image of a cut sphere lies in the cap of its copy. -/
theorem core_cutSphere_mem_range_cap (j : Fin 2) (z : ClosureSphere.{u}) :
    X.capping.core (X.cutSphere j z) ∈ range (X.capping.cap (Fin.cast X.h2.symm j)) := by
  refine ⟨closureSphereToBall ((X.capping.attaching (Fin.cast X.h2.symm j)).symm z), ?_⟩
  rw [X.capping.boundary_eq, Diffeomorph.apply_symm_apply]
  rfl

/-- The cap of copy `j` meets the core exactly in the cut sphere of copy `j`. -/
theorem range_core_inter_cap (j : Fin 2) :
    range X.capping.core ∩ range (X.capping.cap (Fin.cast X.h2.symm j)) =
      range fun z => X.capping.core (X.cutSphere j z) :=
  X.capping.core_cap_intersection _

/-- The differential of a cap is bijective. -/
theorem mfderiv_cap_bijective (j : Fin X.B.sphereCount) (x : ClosedCell 3) :
    Bijective (mfderiv (𝓡∂ 3) X.Q.model (X.capping.cap j) x) := by
  have hinj : Injective (mfderiv (𝓡∂ 3) X.Q.model (X.capping.cap j) x) :=
    (X.capping.cap_embedding j).isImmersion.mfderiv_injective (by simp) x
  exact bijective_of_injective_continuousLinearMap (V := EuclideanSpace ℝ (Fin 3)) hinj

section Side

variable (P : PieceEmbedding W) (j : Fin 2)
  (hside : ∀ q p, p ∈ S.collar.source → P.map q = S.collar p → 0 ≤ cutSideSign j * p.2)

/-- The lifted piece meets the cap of its copy exactly in the cut sphere. -/
theorem range_liftPiece_inter_cap (hzero : S.zeroSphere ⊆ range P.map) :
    range (X.liftPiece P j hside).map ∩ range (X.capping.cap (Fin.cast X.h2.symm j)) =
      range fun z => X.capping.core (X.cutSphere j z) := by
  apply Subset.antisymm
  · rintro y ⟨⟨q, rfl⟩, hcap⟩
    rw [← X.range_core_inter_cap j]
    exact ⟨⟨_, rfl⟩, hcap⟩
  · rintro _ ⟨z, rfl⟩
    refine ⟨?_, X.core_cutSphere_mem_range_cap j z⟩
    obtain ⟨q, hq⟩ := hzero ⟨z, rfl⟩
    exact ⟨q, X.liftPiece_map_of_mem P j hside hq⟩

/-- A lifted piece of interior points has interior points. -/
theorem liftPiece_mem_interior (hint : range P.map ⊆ W.interior) (q : P.Piece) :
    (X.liftPiece P j hside).map q ∈ X.Q.interior := by
  by_cases hq : P.map q ∈ S.zeroSphere
  · obtain ⟨z, hz⟩ := hq
    rw [X.liftPiece_map_of_mem P j hside hz.symm]
    exact range_relativeSphereCap_subset_interior X.capping _ (X.core_cutSphere_mem_range_cap j z)
  · rw [X.liftPiece_map_of_notMem P j hside hq]
    exact X.transport_mem_interior (hint ⟨q, rfl⟩)

/-- **The union of a lifted side piece and its cap is open**, when the half collar of its side lies
in the piece and its model boundary is the seam sphere. -/
theorem isOpen_capUnion (hbd : P.map '' (𝓡∂ 3).boundary P.Piece = S.zeroSphere)
    (hhalf : ∀ z s, 0 ≤ s → s < 1 → S.collar (z, cutSideSign j * s) ∈ range P.map) :
    IsOpen (range (X.liftPiece P j hside).map ∪ range (X.capping.cap (Fin.cast X.h2.symm j))) := by
  set U := range (X.liftPiece P j hside).map ∪ range (X.capping.cap (Fin.cast X.h2.symm j))
  obtain ⟨c, s₀, μ, hs₀, hμ, hsum, hsrc, -, -, hball⟩ :=
    RelativeSphereCapping.exists_shellBallChart X.capping (Fin.cast X.h2.symm j)
  have hcopen : IsOpen (c '' Metric.ball 0 1) :=
    c.toOpenPartialHomeomorph.isOpen_image_of_subset_source Metric.isOpen_ball
      (Metric.ball_subset_closedBall.trans
        ((Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2)).trans hsrc))
  have hcU : c '' Metric.ball 0 1 ⊆ U := by
    rw [hball]
    rintro y (hy | ⟨_, ⟨⟨z, h⟩, hp, rfl⟩, rfl⟩)
    · exact Or.inr hy
    · left
      have hh0 : 0 ≤ h.val 0 := h.2
      have hh1 : h.val 0 < 1 := by
        have : h.val 0 < s₀ := hp
        linarith
      have hh : h = halfPoint (h.val 0) hh0 := (halfPoint_eq_self h hh0 rfl).symm
      obtain ⟨q, hq⟩ := hhalf z (h.val 0) hh0 hh1
      refine ⟨q, ?_⟩
      rw [liftPiece_map, hq, X.sideLift_collar j z hh0 hh1, ← hh]
  have hsub : U ⊆ interior (range (X.liftPiece P j hside).map) ∪ c '' Metric.ball 0 1 := by
    rintro y (⟨q, rfl⟩ | hy)
    · rcases (𝓡∂ 3).isInteriorPoint_or_isBoundaryPoint q with hq | hq
      · exact Or.inl ((X.liftPiece P j hside).toPieceFold.map_mem_interior_range hq)
      · right
        have hx : P.map q ∈ S.zeroSphere := hbd ▸ ⟨q, hq, rfl⟩
        obtain ⟨z, hz⟩ := hx
        rw [X.liftPiece_map_of_mem P j hside hz.symm, hball]
        exact Or.inl (X.core_cutSphere_mem_range_cap j z)
    · right
      rw [hball]
      exact Or.inl hy
  have heq : U = interior (range (X.liftPiece P j hside).map) ∪ c '' Metric.ball 0 1 :=
    Subset.antisymm hsub (union_subset (interior_subset.trans subset_union_left) hcU)
  rw [heq]
  exact isOpen_interior.union hcopen

theorem isCompact_capUnion :
    IsCompact (range (X.liftPiece P j hside).map ∪ range (X.capping.cap (Fin.cast X.h2.symm j))) :=
  (X.liftPiece P j hside).isCompact_range.union
    (isCompact_range (X.capping.cap (Fin.cast X.h2.symm j)).continuous)

/-- **Ball ∪ cap = S³** (actual attaching map). -/
theorem nonempty_capUnion_sphereDiffeomorph
    (e : P.Piece ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3)
    (hbd : P.map '' (𝓡∂ 3).boundary P.Piece = S.zeroSphere)
    (hhalf : ∀ z s, 0 ≤ s → s < 1 → S.collar (z, cutSideSign j * s) ∈ range P.map) :
    Nonempty ((⟨_, X.isOpen_capUnion P j hside hbd hhalf⟩ : TopologicalSpace.Opens X.Q.Carrier)
      ≃ₘ⟮X.Q.model, 𝓡 3⟯ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) := by
  set L := X.liftPiece P j hside
  have hint := X.liftPiece_mem_interior P j hside (range_subset_interior_of_boundary_eq_zeroSphere P hbd)
  let f : ClosedCell 3 → X.Q.Carrier := fun x => L.map (e.symm x)
  have hf : ContMDiff (𝓡∂ 3) X.Q.model ∞ f := L.smooth.comp e.symm.contMDiff
  have hfi : Injective f := L.injective.comp e.symm.injective
  have hfb : ∀ x, Bijective (mfderiv (𝓡∂ 3) X.Q.model f x) := by
    intro x
    change Bijective (mfderiv (𝓡∂ 3) X.Q.model (L.map ∘ e.symm) x)
    rw [mfderiv_comp x (L.smooth.mdifferentiableAt (by simp))
      (e.symm.contMDiff.mdifferentiableAt (by simp))]
    exact (L.mfderiv_bijective _).comp
      (e.symm.mfderivToContinuousLinearEquiv (by simp) x).bijective
  refine nonempty_sphereDiffeomorph_of_closedCell_cover _ ?_ f
    (X.capping.cap (Fin.cast X.h2.symm j)) hf (X.capping.cap_embedding _).contMDiff hfi
    (X.capping.cap_embedding _).isEmbedding.injective hfb (X.mfderiv_cap_bijective _) ?_
  · rintro y (⟨q, rfl⟩ | hy)
    · exact hint q
    · exact range_relativeSphereCap_subset_interior X.capping _ hy
  · ext y
    constructor
    · rintro (⟨x, rfl⟩ | hy)
      · exact Or.inl ⟨e.symm x, rfl⟩
      · exact Or.inr hy
    · rintro (⟨q, rfl⟩ | hy)
      · have hq : ∀ q' : P.Piece, f (e q') = X.capping.core (X.sideLift j (P.map q')) :=
          fun q' => congrArg (fun r => X.capping.core (X.sideLift j (P.map r)))
            (e.symm_apply_apply q')
        exact Or.inl ⟨e q, hq q⟩
      · exact Or.inr hy

end Side

end SphereCutCapped

/-! ## Certificate level -/

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)
  (c : Fin D.sphereSeamCount) (X : SphereCutCapped W (D.sphereSeam c) E)

/-- The half collar of side `b` lies in the side vertex `b`. -/
theorem halfCollar_mem_image (b : Bool) (z : ClosureSphere.{u}) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s < 1) :
    (D.sphereSeam c).collar (z, cutSideSign (sideCopy b) * s) ∈
      range (D.vertex (D.sphereSide c b)).piece.map := by
  rw [← Vertex.image_eq_range_piece, cutSideSign_sideCopy]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    exact D.sphereSide_pos c z s hs0 hs1
  · simp only [↓reduceIte, neg_mul, one_mul]
    exact D.sphereSide_neg c z (-s) (by linarith) (by linarith)

/-- The model boundary of a ball side vertex is the seam sphere. -/
theorem boundaryImage_eq_zeroSphere_of_isBall (b : Bool)
    (hk : (D.vertex (D.sphereSide c b)).IsBall) :
    (D.vertex (D.sphereSide c b)).boundaryImage = (D.sphereSeam c).zeroSphere := by
  obtain ⟨f, hfo, hfk⟩ := D.sphereSeam_face c b
  rw [← D.face_eq_boundaryImage_of_isBall hk hfo, (D.face_sphereSeam f c b hfk).1]
  rfl

/-- The side copy of the side vertex `b` (definitionally the copy used by `liftVertex`). -/
theorem sideCopy_vertexSide (b : Bool) :
    sideCopy (D.vertexSide c (D.sphereSide c b)) = sideCopy b := by
  rw [D.vertexSide_sphereSide]

/-- **S3a, ball ∪ cap = S³** (actual attaching map): the lifted ball side vertex and the cap of its
copy form an open set of the capped carrier diffeomorphic to the round `S³`. -/
theorem capUnion_ball_sphere (b : Bool) (hk : (D.vertex (D.sphereSide c b)).IsBall) :
    ∃ hU : IsOpen (range (D.liftVertex c X (D.sphereSide c b)).map ∪
        range (X.capping.cap (Fin.cast X.h2.symm (sideCopy b)))),
      IsCompact (range (D.liftVertex c X (D.sphereSide c b)).map ∪
        range (X.capping.cap (Fin.cast X.h2.symm (sideCopy b)))) ∧
      Nonempty ((⟨_, hU⟩ : TopologicalSpace.Opens X.Q.Carrier) ≃ₘ⟮X.Q.model, 𝓡 3⟯
        Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) := by
  set v := D.sphereSide c b
  have hcap : X.capping.cap (Fin.cast X.h2.symm (sideCopy (D.vertexSide c v))) =
      X.capping.cap (Fin.cast X.h2.symm (sideCopy b)) := by
    rw [D.sideCopy_vertexSide c b]
  have hbd : (D.vertex v).piece.map '' (𝓡∂ 3).boundary (D.vertex v).piece.Piece =
      (D.sphereSeam c).zeroSphere := D.boundaryImage_eq_zeroSphere_of_isBall c b hk
  have hhalf : ∀ z s, 0 ≤ s → s < 1 → (D.sphereSeam c).collar
      (z, cutSideSign (sideCopy (D.vertexSide c v)) * s) ∈ range (D.vertex v).piece.map := by
    intro z s hs0 hs1
    rw [D.sideCopy_vertexSide c b]
    exact D.halfCollar_mem_image c b z hs0 hs1
  have e : (D.vertex v).piece.Piece ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3 := hk.piece_eq ▸ hk.model
  have hopen := X.isOpen_capUnion (D.vertex v).piece (sideCopy (D.vertexSide c v))
    (fun _ _ hp h => D.vertex_side_condition c v hp h) hbd hhalf
  have hsph := X.nonempty_capUnion_sphereDiffeomorph (D.vertex v).piece
    (sideCopy (D.vertexSide c v)) (fun _ _ hp h => D.vertex_side_condition c v hp h) e hbd hhalf
  have hset : range (D.liftVertex c X v).map ∪
      range (X.capping.cap (Fin.cast X.h2.symm (sideCopy (D.vertexSide c v)))) =
      range (D.liftVertex c X v).map ∪ range (X.capping.cap (Fin.cast X.h2.symm (sideCopy b))) := by
    rw [hcap]
  refine ⟨hset ▸ hopen, hset ▸ X.isCompact_capUnion _ _ _, ?_⟩
  have hopens : (⟨_, hopen⟩ : TopologicalSpace.Opens X.Q.Carrier) = ⟨_, hset ▸ hopen⟩ :=
    TopologicalSpace.Opens.ext hset
  rw [← hopens]
  exact hsph

/-- The capped ball side is a whole component of the capped carrier: the one containing its cap. -/
theorem capUnion_eq_componentPiece (b : Bool) (hk : (D.vertex (D.sphereSide c b)).IsBall)
    (DQ : X.Q.Components) :
    range (D.liftVertex c X (D.sphereSide c b)).map ∪
        range (X.capping.cap (Fin.cast X.h2.symm (sideCopy b))) =
      (DQ.piece (X.spherePiece DQ (Fin.cast X.h2.symm (sideCopy b))) : Set X.Q.Carrier) := by
  obtain ⟨hU, hUc, -⟩ := D.capUnion_ball_sphere c X b hk
  set U := range (D.liftVertex c X (D.sphereSide c b)).map ∪
    range (X.capping.cap (Fin.cast X.h2.symm (sideCopy b)))
  set i := X.spherePiece DQ (Fin.cast X.h2.symm (sideCopy b))
  have hclopen : IsClopen U := ⟨hUc.isClosed, hU⟩
  have hpi : IsClopen (DQ.piece i : Set X.Q.Carrier) := isClopen_componentsPiece DQ i
  let z₀ : ClosureSphere.{u} :=
    @Nonempty.some _ (@ConnectedSpace.toNonempty _ _ closureSphere_connectedSpace)
  have hx₀i : X.capping.core (X.cutSphere (sideCopy b) z₀) ∈ (DQ.piece i : Set X.Q.Carrier) :=
    X.sphere_mem_spherePiece DQ _ z₀
  have hx₀U : X.capping.core (X.cutSphere (sideCopy b) z₀) ∈ U :=
    Or.inr (X.core_cutSphere_mem_range_cap _ z₀)
  have hcapconn : IsConnected (range (X.capping.cap (Fin.cast X.h2.symm (sideCopy b)))) := by
    have := closedCell_three_connectedSpace
    exact isConnected_range (X.capping.cap _).continuous
  have hLconn : IsConnected (range (D.liftVertex c X (D.sphereSide c b)).map) :=
    (D.liftVertex c X (D.sphereSide c b)).isConnected_range
  have hUconn : IsPreconnected U := by
    refine hLconn.isPreconnected.union (X.capping.core (X.cutSphere (sideCopy b) z₀)) ?_
      (X.core_cutSphere_mem_range_cap _ z₀) hcapconn.isPreconnected
    obtain ⟨q, hq⟩ : (D.sphereSeam c).collar (z₀, 0) ∈ range (D.vertex (D.sphereSide c b)).piece.map :=
      by
        rw [← Vertex.image_eq_range_piece]
        exact D.sphereSeam_zero_mem c b z₀
    exact ⟨q, D.liftVertex_map_of_mem c X b hq⟩
  have hpconn : IsPreconnected (DQ.piece i : Set X.Q.Carrier) := by
    have := DQ.connected i
    exact isPreconnected_iff_preconnectedSpace.mpr inferInstance
  exact Subset.antisymm (hUconn.subset_isClopen hpi ⟨_, hx₀U, hx₀i⟩)
    (hpconn.subset_isClopen hclopen ⟨_, hx₀i, hx₀U⟩)

/-- **S3a, consumer form**: the component of the capped carrier containing the cap of a ball side
is the round `S³`. -/
theorem componentCarrier_sphere_of_ball (b : Bool) (hk : (D.vertex (D.sphereSide c b)).IsBall)
    (DQ : X.Q.Components) :
    Nonempty ((GC.Topology.componentCarrier X.Q DQ
        (X.spherePiece DQ (Fin.cast X.h2.symm (sideCopy b)))).Carrier ≃ₘ⟮
      (GC.Topology.componentCarrier X.Q DQ
        (X.spherePiece DQ (Fin.cast X.h2.symm (sideCopy b)))).model, 𝓡 3⟯
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) := by
  obtain ⟨hU, -, ⟨φ⟩⟩ := D.capUnion_ball_sphere c X b hk
  have hset := D.capUnion_eq_componentPiece c X b hk DQ
  have hopens : (⟨_, hU⟩ : TopologicalSpace.Opens X.Q.Carrier) =
      DQ.piece (X.spherePiece DQ (Fin.cast X.h2.symm (sideCopy b))) :=
    TopologicalSpace.Opens.ext hset
  rw [hopens] at φ
  exact ⟨φ⟩

end DecompositionCertificate

end GC.GraphManifold.Assembly
