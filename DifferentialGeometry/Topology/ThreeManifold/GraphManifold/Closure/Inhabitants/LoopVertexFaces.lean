import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopArcSublevel

/-!
The actual original ball and deep solid core give two native vertices with their WHOLE faces.
The original nonempty handle and SAME circle region retain genuine ambient cover and interiors.
-/
set_option autoImplicit false
noncomputable section
open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology
open GC.GraphManifold GC.Endpoint
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly

private def loopVertexIndex : Fin standardLoopBallHandleCycle.len :=
  ⟨0,standardLoopBallHandleCycle.len_pos⟩

def loopBallVertexModel : Vertex (NoCuts.carrier standardThreeSphereLift.{0}) :=
  .zero (standardLoopBallHandleCycle.ball loopVertexIndex)
    (.ball (standardLoopBallHandleCycle.ballModel loopVertexIndex))

def loopCertificateVertex (k : Fin 2) : Vertex (NoCuts.carrier standardThreeSphereLift.{0}) :=
  if k = 0 then loopBallVertexModel else loopComplementModel

def loopCertificateFace (f : Fin 2) : Set SphereCarrier.{0} :=
  if f = 0 then loopBallWholeFace else loopComplementFace

def loopCertificateFaceModel (f : Fin 2) :
    (loopCertificateFace f ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ⊕
    (loopCertificateFace f ≃ₜ Circle × Circle) := by
  by_cases hf : f = 0
  · rw [loopCertificateFace,ite_eq_left hf]
    exact Sum.inl loopBallWholeFaceModel
  · rw [loopCertificateFace,ite_eq_right hf]
    exact Sum.inr loopComplementFaceModel

theorem loopCertificateFace_boundary (f : Fin 2) :
    loopCertificateFace f = (loopCertificateVertex f).boundaryImage := by
  fin_cases f <;> rfl

theorem loopCertificateFace_closed (f : Fin 2) : IsClosed (loopCertificateFace f) := by
  fin_cases f
  · change IsClosed loopBallWholeFace
    rw [loopBallWholeFace_frontier]
    exact isClosed_frontier
  · exact loopComplementFace_closed

theorem loopCertificateFace_disjoint :
    Disjoint (loopCertificateFace 0) (loopCertificateFace 1) := by
  change Disjoint loopBallWholeFace loopComplementFace
  apply (loopBall_core_disjoint loopVertexIndex).mono
  · rintro p ⟨q,_,hp⟩
    exact ⟨q,hp⟩
  · rintro p ⟨q,_,hp⟩
    exact ⟨q,hp⟩

theorem loopCertificateVertex_disjoint : Pairwise fun k k' : Fin 2 =>
    Disjoint (interior (loopCertificateVertex k).image)
      (interior (loopCertificateVertex k').image) := by
  intro k k' hne
  fin_cases k <;> fin_cases k'
  · exact False.elim (hne rfl)
  · exact (loopBall_core_disjoint loopVertexIndex).mono interior_subset interior_subset
  · exact (loopBall_core_disjoint loopVertexIndex).symm.mono interior_subset interior_subset
  · exact False.elim (hne rfl)

theorem loopCertificateVertex_handle_disjoint (k : Fin 2) :
    Disjoint (interior (loopCertificateVertex k).image) (interior (Set.range
      (standardLoopBallHandleCycle.handle ⟨0,standardLoopBallHandleCycle.len_pos⟩).map)) := by
  fin_cases k
  · exact loopBall_handle_interiors_disjoint loopVertexIndex loopVertexIndex
  · exact (loopHandle_core_disjoint loopVertexIndex).symm.mono interior_subset interior_subset

theorem loopCertificateVertex_region_disjoint (k : Fin 2) :
    Disjoint (interior loopCircleRegion) (interior (loopCertificateVertex k).image) := by
  fin_cases k
  · exact loopCircleRegion_ball_disjoint loopVertexIndex
  · exact loopCircleRegion_core_disjoint

theorem loopCertificateVertex_cover :
    (⋃ k : Fin 2, (loopCertificateVertex k).image) ∪ Set.range
      (standardLoopBallHandleCycle.handle ⟨0,standardLoopBallHandleCycle.len_pos⟩).map ∪
      loopCircleRegion = Set.univ := by
  have hu : (⋃ k : Fin 2, (loopCertificateVertex k).image) =
      Set.range (standardLoopBallHandleCycle.ball loopVertexIndex).map ∪
      Set.range loopComplementVertex.map := by
    ext p
    simp only [mem_iUnion,mem_union,Fin.exists_fin_two]
    rfl
  rw [hu]
  change (Set.range (standardLoopBallHandleCycle.ball loopVertexIndex).map ∪
    Set.range loopComplementVertex.map) ∪ Set.range
    (standardLoopBallHandleCycle.handle loopVertexIndex).map ∪ loopCircleRegion = Set.univ
  have hs : ∀ k : Fin standardLoopBallHandleCycle.len, k = loopVertexIndex := by
    intro k
    apply Fin.ext
    have hbound : standardLoopBallHandleCycle.len ≤ 1 := by
      rw [standardLoopBallHandleCycle_len]
    have hlt := lt_of_lt_of_le k.isLt hbound
    change k.val = 0
    omega
  have hb : (⋃ k, Set.range (standardLoopBallHandleCycle.ball k).map) =
      Set.range (standardLoopBallHandleCycle.ball loopVertexIndex).map := by
    ext p
    constructor
    · intro hp
      obtain ⟨k,hk⟩ := mem_iUnion.mp hp
      rwa [hs k] at hk
    · exact fun hp => mem_iUnion.mpr ⟨loopVertexIndex,hp⟩
  have hh : (⋃ k, Set.range (standardLoopBallHandleCycle.handle k).map) =
      Set.range (standardLoopBallHandleCycle.handle loopVertexIndex).map := by
    ext p
    constructor
    · intro hp
      obtain ⟨k,hk⟩ := mem_iUnion.mp hp
      rwa [hs k] at hk
    · exact fun hp => mem_iUnion.mpr ⟨loopVertexIndex,hp⟩
  have hc := loopCircleRegion_cover
  rw [hb,hh] at hc
  convert hc using 1
  ac_rfl

end GC.GraphManifold.Assembly
