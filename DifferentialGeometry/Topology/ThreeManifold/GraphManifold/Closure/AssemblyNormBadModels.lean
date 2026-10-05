import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyNormMeasure
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyFC42ModelsApplications
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereRecPorts

/-!
# FC42 normalization, packet N4 (a): the model classification of bad vertices

Lane ASM-NRM (frozen text `build-logs/scratch/ASM-NRM/Targets.lean`, section N4 (a)).

* `Vertex.boundaryImage_eq_iUnion_of_raw`: if the piece of a vertex is diffeomorphic to a carrier
  with a raw presentation, its model-boundary image is the union of the finitely many embedded tori
  `piece.map ∘ ψ ∘ torusMap i` (pairwise disjoint, from the disjoint port collars).
* `face_homeomorph_torus_of_raw`: then every face of that vertex IS one of these tori (it is a
  connected component of the boundary image, G3), so it is homeomorphic to `Circle × Circle`.
* `vertex_cases_of_face_homeomorph_sphere`: the owner of a face homeomorphic to the two-sphere is a
  ball, a punctured `RP³` or an `S² × I` — the torus-faced models (solid torus, twisted `I`-bundle,
  `T² × I`, cusp core) have raw presentations (`Vertex.rawPiece_of_torusFaced`, built), and a two-sphere
  is not a torus; closed zero pieces and slim circle bundles have empty boundary (no face).
* `vertex_cases_of_mem_badVertexSet`: the frozen N4 (a) classification of bad vertices.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-! ## The boundary image of a vertex with a raw model -/

section RawBoundary

variable {W : CompactCarrier.{u}} {X : CompactCarrier.{u}}

/-- The embedded boundary tori of a vertex whose piece is diffeomorphic to a raw-presented
carrier. -/
def Vertex.rawTorus (v : Vertex W) (R : RawGraphPresentation X)
    (ψ : X.Carrier ≃ₘ⟮X.model, 𝓡∂ 3⟯ v.piece.Piece) (i : Fin R.externalCount) : Torus → W.Carrier :=
  fun t => v.piece.map (ψ (R.external.torusMap i t))

theorem Vertex.continuous_rawTorus (v : Vertex W) (R : RawGraphPresentation X)
    (ψ : X.Carrier ≃ₘ⟮X.model, 𝓡∂ 3⟯ v.piece.Piece) (i : Fin R.externalCount) :
    Continuous (v.rawTorus R ψ i) :=
  v.piece.continuous_map.comp (ψ.continuous.comp (R.external.torusMap_isEmbedding i).continuous)

theorem Vertex.injective_rawTorus (v : Vertex W) (R : RawGraphPresentation X)
    (ψ : X.Carrier ≃ₘ⟮X.model, 𝓡∂ 3⟯ v.piece.Piece) (i : Fin R.externalCount) :
    Injective (v.rawTorus R ψ i) :=
  v.piece.injective.comp (ψ.injective.comp (R.external.torusMap_isEmbedding i).injective)

theorem Vertex.boundaryImage_eq_iUnion_of_raw (v : Vertex W) (R : RawGraphPresentation X)
    (ψ : X.Carrier ≃ₘ⟮X.model, 𝓡∂ 3⟯ v.piece.Piece) :
    v.boundaryImage = ⋃ i, range (v.rawTorus R ψ i) := by
  have hpre := ψ.isLocalDiffeomorph.preimage_boundary (by simp)
  ext x
  simp only [Vertex.boundaryImage, mem_image, mem_iUnion, mem_range]
  constructor
  · rintro ⟨q, hq, rfl⟩
    have hq' : ψ.symm q ∈ X.model.boundary X.Carrier := by
      have : ψ.symm q ∈ ψ ⁻¹' (𝓡∂ 3).boundary v.piece.Piece := by
        rw [mem_preimage, Diffeomorph.apply_symm_apply]
        exact hq
      rwa [hpre] at this
    rw [R.external_exhausted] at hq'
    obtain ⟨i, t, ht⟩ := mem_iUnion.mp hq'
    refine ⟨i, t, ?_⟩
    change v.piece.map (ψ (R.external.torusMap i t)) = v.piece.map q
    rw [ht, Diffeomorph.apply_symm_apply]
  · rintro ⟨i, t, rfl⟩
    refine ⟨ψ (R.external.torusMap i t), ?_, rfl⟩
    have h : R.external.torusMap i t ∈ X.model.boundary X.Carrier := by
      rw [R.external_exhausted]
      exact mem_iUnion.mpr ⟨i, t, rfl⟩
    rw [← hpre] at h
    exact h

theorem Vertex.disjoint_rawTorus (v : Vertex W) (R : RawGraphPresentation X)
    (ψ : X.Carrier ≃ₘ⟮X.model, 𝓡∂ 3⟯ v.piece.Piece) {i j : Fin R.externalCount} (hij : i ≠ j) :
    Disjoint (range (v.rawTorus R ψ i)) (range (v.rawTorus R ψ j)) := by
  rw [Set.disjoint_left]
  rintro _ ⟨t, rfl⟩ ⟨s, hs⟩
  have h := ψ.injective (v.piece.injective hs)
  exact Set.disjoint_left.mp (R.external.disjoint hij.symm)
    (PortRestriction.torusMap_mem_target R.external j s)
    (h ▸ PortRestriction.torusMap_mem_target R.external i t)

end RawBoundary

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)

/-- **A face of a vertex with a raw model is one of its boundary tori.** -/
theorem face_homeomorph_torus_of_raw (f : Fin D.faceCount) {X : CompactCarrier.{u}}
    (R : RawGraphPresentation X)
    (ψ : X.Carrier ≃ₘ⟮X.model, 𝓡∂ 3⟯ (D.vertex (D.faceOwner f)).piece.Piece) :
    Nonempty (D.face f ≃ₜ Circle × Circle) := by
  set v := D.vertex (D.faceOwner f)
  have hB := v.boundaryImage_eq_iUnion_of_raw R ψ
  obtain ⟨z, hz⟩ := D.face_nonempty f
  have hzB : z ∈ v.boundaryImage := D.face_subset_boundaryImage f hz
  rw [hB] at hzB
  obtain ⟨i₀, hzi⟩ := mem_iUnion.mp hzB
  have hcont := v.continuous_rawTorus R ψ i₀
  have hconn : IsPreconnected (range (v.rawTorus R ψ i₀)) := isPreconnected_range hcont
  have hsub : range (v.rawTorus R ψ i₀) ⊆ D.face f :=
    D.subset_face_of_isPreconnected f hconn
      (fun x hx => hB ▸ mem_iUnion.mpr ⟨i₀, hx⟩) hzi hz
  -- the face lies in the torus `i₀`: the other tori form a closed set disjoint from it
  let B : Set W.Carrier := ⋃ (j : Fin R.externalCount) (_ : j ≠ i₀), range (v.rawTorus R ψ j)
  have hBc : IsClosed B := isClosed_iUnion_of_finite fun j => isClosed_iUnion_of_finite fun _ =>
    (isCompact_range (v.continuous_rawTorus R ψ j)).isClosed
  have hAc : IsClosed (range (v.rawTorus R ψ i₀)) := (isCompact_range hcont).isClosed
  have hcover : D.face f ⊆ range (v.rawTorus R ψ i₀) ∪ B := by
    intro x hx
    have hxB : x ∈ v.boundaryImage := D.face_subset_boundaryImage f hx
    rw [hB] at hxB
    obtain ⟨j, hj⟩ := mem_iUnion.mp hxB
    by_cases hji : j = i₀
    · exact Or.inl (hji ▸ hj)
    · exact Or.inr (mem_iUnion₂.mpr ⟨j, hji, hj⟩)
  have hdisj : Disjoint (range (v.rawTorus R ψ i₀)) B :=
    disjoint_iUnion_right.mpr fun j => disjoint_iUnion_right.mpr fun hji =>
      v.disjoint_rawTorus R ψ (Ne.symm hji)
  have hpre := (D.isConnected_face f).isPreconnected
  rw [isPreconnected_iff_subset_of_disjoint_closed] at hpre
  have hempty : D.face f ∩ (range (v.rawTorus R ψ i₀) ∩ B) = ∅ := by
    rw [hdisj.inter_eq, inter_empty]
  have heq : D.face f = range (v.rawTorus R ψ i₀) := by
    refine Subset.antisymm ?_ hsub
    rcases hpre _ _ hAc hBc hcover hempty with h | h
    · exact h
    · exact (Set.disjoint_left.mp hdisj hzi (h hz)).elim
  exact ⟨(Homeomorph.setCongr heq).trans
    (homeomorphRangeOfTorus hcont (v.injective_rawTorus R ψ i₀))⟩

/-- A face is nonempty, so its owner has a nonempty model boundary. -/
theorem boundaryImage_nonempty_of_face (f : Fin D.faceCount) :
    (D.vertex (D.faceOwner f)).boundaryImage.Nonempty := by
  obtain ⟨z, hz⟩ := D.face_nonempty f
  exact ⟨z, D.face_subset_boundaryImage f hz⟩

/-- **Classification.** The owner of a face homeomorphic to the two-sphere is a ball, a punctured
`RP³` or an `S² × I`. -/
theorem vertex_cases_of_face_homeomorph_sphere (f : Fin D.faceCount)
    (φ : D.face f ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    (D.vertex (D.faceOwner f)).IsBall ∨
    (∃ (P : PieceEmbedding W)
      (c : OrientedBallChart projectiveThreeSpaceLift.{u}.toClosedOrientedManifold)
      (g : P.Piece → projectiveThreeSpaceLift.{u}.Carrier) (hg : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ g)
      (hr : range g = {x | x ∉ c.chart '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1}),
      D.vertex (D.faceOwner f) = .zero P (.puncturedRP3 c g hg hr)) ∨
    ∃ (P : PieceEmbedding W)
      (e : (ClosureSphere.{u} × Icc (0 : ℝ) 1) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1), 𝓡∂ 3⟯ P.Piece),
      D.vertex (D.faceOwner f) = .slim P (.sphereInterval e) := by
  have htorus : ∀ hv : (∃ P e, D.vertex (D.faceOwner f) = .zero P (.solidTorus e)) ∨
      (∃ P e, D.vertex (D.faceOwner f) = .zero P (.twistedIBundle e)) ∨
      (∃ P e, D.vertex (D.faceOwner f) = .slim P (.torusInterval e)) ∨
      (∃ P e, D.vertex (D.faceOwner f) = .cuspCore P e), False := by
    intro hv
    obtain ⟨X, ⟨R⟩, ⟨ψ⟩⟩ := (D.vertex (D.faceOwner f)).rawPiece_of_torusFaced hv
    obtain ⟨τ⟩ := D.face_homeomorph_torus_of_raw f R ψ
    exact false_of_homeomorph_sphereTwo_of_homeomorph_torus φ τ
  have hempty : (D.vertex (D.faceOwner f)).boundaryImage.Nonempty :=
    D.boundaryImage_nonempty_of_face f
  rcases hk : D.vertex (D.faceOwner f) with ⟨P, m⟩ | C | ⟨P, m⟩ | ⟨P, e⟩
  · rcases m with e | e | e | ⟨c, g, hg, hr⟩
    · exact Or.inl ⟨P, e, rfl⟩
    · exact (htorus (Or.inl ⟨P, e, hk⟩)).elim
    · exact (htorus (Or.inr (Or.inl ⟨P, e, hk⟩))).elim
    · exact Or.inr (Or.inl ⟨P, c, g, hg, hr, rfl⟩)
  · rw [hk] at hempty
    obtain ⟨_, q, hq, -⟩ := hempty
    change q ∈ (𝓡∂ 3).boundary C.piece.Piece at hq
    rw [C.boundary_empty] at hq
    exact hq.elim
  · rcases m with e | e | ⟨p, hp, hsub, fib, hcl⟩
    · exact Or.inr (Or.inr ⟨P, e, rfl⟩)
    · exact (htorus (Or.inr (Or.inr (Or.inl ⟨P, e, hk⟩)))).elim
    · rw [hk] at hempty
      obtain ⟨_, q, hq, -⟩ := hempty
      change q ∈ (𝓡∂ 3).boundary P.Piece at hq
      rw [hcl] at hq
      exact hq.elim
  · exact (htorus (Or.inr (Or.inr (Or.inr ⟨P, e, hk⟩)))).elim

/-- **N4, model classification.** A bad vertex is a punctured `RP³` or an `S² × I`. -/
theorem vertex_cases_of_mem_badVertexSet {k : Fin D.vertexCount} (hk : k ∈ D.badVertexSet) :
    (∃ (P : PieceEmbedding W)
      (c : OrientedBallChart projectiveThreeSpaceLift.{u}.toClosedOrientedManifold)
      (f : P.Piece → projectiveThreeSpaceLift.{u}.Carrier) (hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f)
      (hr : range f = {x | x ∉ c.chart '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1}),
      D.vertex k = .zero P (.puncturedRP3 c f hf hr)) ∨
    ∃ (P : PieceEmbedding W)
      (e : (ClosureSphere.{u} × Icc (0 : ℝ) 1) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1), 𝓡∂ 3⟯ P.Piece),
      D.vertex k = .slim P (.sphereInterval e) := by
  obtain ⟨hnb, f, hfo, -, e, -⟩ := mem_badVertexSet_iff.mp hk
  subst hfo
  rcases D.vertex_cases_of_face_homeomorph_sphere f e with hb | h | h
  · exact (hnb hb).elim
  · exact Or.inl h
  · exact Or.inr h

end DecompositionCertificate

end GC.GraphManifold.Assembly
