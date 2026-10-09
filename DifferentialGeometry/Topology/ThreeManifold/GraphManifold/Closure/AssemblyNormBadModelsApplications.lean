import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyNormBadModels

/-!
# Consumers of packet N4 (a): the bad-vertex dispatch of the FC42 sphere step

* `exists_bad_model_of_badVertexCount_pos`: a positive bad count gives a bad vertex that is a
  punctured `RP³` (internal operation N2) or an `S² × I` (internal operation N3) — the dispatch of the
  bad-vertex case of the sphere step.
* `exists_bad_model_of_sphereMeasure_pos`: with no sphere seam, a positive measure is a positive
  bad count, hence the same dispatch.
* `sphereSide_cases`: a side of a sphere seam is a ball, a punctured `RP³` or an `S² × I` (its seam
  face is the homeomorphic image of the seam sphere).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)

/-- **The bad-vertex dispatch.** -/
theorem exists_bad_model_of_badVertexCount_pos (h : 0 < D.badVertexCount) :
    ∃ k ∈ D.badVertexSet,
      (∃ (P : PieceEmbedding W)
        (c : OrientedBallChart projectiveThreeSpaceLift.{u}.toClosedOrientedManifold)
        (f : P.Piece → projectiveThreeSpaceLift.{u}.Carrier)
        (hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f)
        (hr : range f = {x | x ∉ c.chart '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1}),
        D.vertex k = .zero P (.puncturedRP3 c f hf hr)) ∨
      ∃ (P : PieceEmbedding W)
        (e : (ClosureSphere.{u} × Icc (0 : ℝ) 1) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1), 𝓡∂ 3⟯ P.Piece),
        D.vertex k = .slim P (.sphereInterval e) := by
  obtain ⟨k, hk⟩ := D.exists_mem_badVertexSet h
  exact ⟨k, hk, D.vertex_cases_of_mem_badVertexSet hk⟩

/-- With no sphere seam, a positive measure dispatches to a bad vertex. -/
theorem exists_bad_model_of_sphereMeasure_pos (hσ : D.sphereSeamCount = 0)
    (hμ : 0 < D.sphereMeasure) :
    ∃ k ∈ D.badVertexSet,
      (∃ (P : PieceEmbedding W)
        (c : OrientedBallChart projectiveThreeSpaceLift.{u}.toClosedOrientedManifold)
        (f : P.Piece → projectiveThreeSpaceLift.{u}.Carrier)
        (hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f)
        (hr : range f = {x | x ∉ c.chart '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1}),
        D.vertex k = .zero P (.puncturedRP3 c f hf hr)) ∨
      ∃ (P : PieceEmbedding W)
        (e : (ClosureSphere.{u} × Icc (0 : ℝ) 1) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1), 𝓡∂ 3⟯ P.Piece),
        D.vertex k = .slim P (.sphereInterval e) := by
  apply D.exists_bad_model_of_badVertexCount_pos
  unfold sphereMeasure at hμ
  omega

/-- **A side of a sphere seam** is a ball, a punctured `RP³` or an `S² × I`. -/
theorem sphereSide_cases (c : Fin D.sphereSeamCount) (b : Bool) :
    (D.vertex (D.sphereSide c b)).IsBall ∨
    (∃ (P : PieceEmbedding W)
      (c' : OrientedBallChart projectiveThreeSpaceLift.{u}.toClosedOrientedManifold)
      (f : P.Piece → projectiveThreeSpaceLift.{u}.Carrier)
      (hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f)
      (hrange : range f = {x | x ∉ c'.chart '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1}),
      D.vertex (D.sphereSide c b) = .zero P (.puncturedRP3 c' f hf hrange)) ∨
    (∃ (P : PieceEmbedding W)
      (e : (ClosureSphere.{u} × Icc (0 : ℝ) 1) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1), 𝓡∂ 3⟯ P.Piece),
      D.vertex (D.sphereSide c b) = .slim P (.sphereInterval e)) := by
  obtain ⟨f, hfo, hfk⟩ := D.sphereSeam_face c b
  have hface := (D.face_sphereSeam f c b hfk).1
  -- the seam face is the injective continuous image of the seam sphere
  let g : ClosureSphere.{u} → W.Carrier := fun z => (D.sphereSeam c).collar (z, 0)
  have hsrc : ∀ z : ClosureSphere.{u}, (z, (0 : ℝ)) ∈ (D.sphereSeam c).collar.source := fun z => by
    rw [(D.sphereSeam c).source_eq]
    simp [sphereSignedCollarSource]
  have hg : Continuous g :=
    (D.sphereSeam c).collar.contMDiffOn.continuousOn.comp_continuous
      (continuous_id.prodMk continuous_const) hsrc
  have hginj : Injective g := fun z z' h =>
    congrArg Prod.fst ((D.sphereSeam c).collar.toOpenPartialHomeomorph.injOn (hsrc z) (hsrc z') h)
  have hS : Nonempty (D.face f ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
    have : ClosureSphere.{u} ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := Homeomorph.ulift
    exact ⟨(Homeomorph.setCongr hface).trans
      (((hg.isClosedEmbedding hginj).isEmbedding.toHomeomorph).symm.trans this)⟩
  obtain ⟨φ⟩ := hS
  have h := D.vertex_cases_of_face_homeomorph_sphere f φ
  rwa [hfo] at h

end DecompositionCertificate

end GC.GraphManifold.Assembly
