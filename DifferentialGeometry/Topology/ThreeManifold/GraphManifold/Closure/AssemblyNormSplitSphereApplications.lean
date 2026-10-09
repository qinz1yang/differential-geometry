import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyNormSplitSphere
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyNormBadModelsApplications

/-!
# FC42 normalization, packet N3a: the split of a bad `S² × I` vertex

Lane ASM-NRM3 (frozen statement `stub_N3a_split`, `build-logs/scratch/ASM-NRM/Targets.lean` v2).

* `DecompositionCertificate.exists_splitSphereInterval` (**N3a**): for a certificate without sphere
  seams and closed zero vertices and a bad vertex `k = .slim P (.sphereInterval e)`, a certificate
  `D″` on the same `W, E` with exactly one sphere seam `c″`, whose bad vertices off `c″` number at most
  `b(D) - 1`, without closed zero vertices, inheriting the rim-product clause. Construction: N1 shrinks
  the rim charts off the compact middle zone `P (e (S² × [1/4, 3/4]))`
  (`exists_shrinkRims_avoiding_interior`), then `splitSphereInterval` splits `k` at its middle sphere.
  Deviation from the frozen text: the instance argument `[ConnectedSpace W.Carrier]` is not used and
  is dropped (strengthening); the verbatim form is kept as an `example`.
* Consumer `exists_puncturedRP3_or_splitSphereInterval`: with no sphere seam and positive measure,
  either a bad punctured `RP³` vertex exists (the case of N2a) or N3a applies.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

namespace DecompositionCertificate

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n} (D : DecompositionCertificate W E)

/-- **N3a. The split of a bad `S² × I` vertex at its middle sphere** (after N1): a certificate on
the same `W, E` with one sphere seam whose non-side bad vertices are at most the bad vertices of `D`
other than `k`, without closed zero vertices, inheriting the rim-product clause. -/
theorem exists_splitSphereInterval (hnz : ∀ k C, D.vertex k ≠ .closedZero C)
    (hσ : D.sphereSeamCount = 0) {k : Fin D.vertexCount} (hk : k ∈ D.badVertexSet)
    {P : PieceEmbedding W}
    {e : (ClosureSphere.{u} × Icc (0 : ℝ) 1) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1), 𝓡∂ 3⟯ P.Piece}
    (hv : D.vertex k = .slim P (.sphereInterval e)) :
    ∃ (D'' : DecompositionCertificate W E) (c'' : Fin D''.sphereSeamCount),
      D''.sphereSeamCount = 1 ∧
      (D''.badVertexSet.filter fun k => ∀ b, k ≠ D''.sphereSide c'' b).card + 1 ≤
        D.badVertexCount ∧
      (∀ k C, D''.vertex k ≠ .closedZero C) ∧ (D.RimProduct → D''.RimProduct) := by
  have hK : P.middleZone e ⊆ interior (D.vertex k).image ∩ W.interior := by
    rw [image_eq_of_sphereInterval hv]
    exact P.middleZone_subset e
  obtain ⟨ε, hε, hε1, hdisj, -, -, hrp⟩ :=
    D.exists_shrinkRims_avoiding_interior (P.isCompact_middleZone e) hK
  have hσ' : (D.shrinkRims ε hε hε1).sphereSeamCount = 0 := hσ
  have hv' : (D.shrinkRims ε hε hε1).vertex k = .slim P (.sphereInterval e) := hv
  have hk' : k ∈ (D.shrinkRims ε hε hε1).badVertexSet := by
    rw [D.badVertexSet_shrinkRims ε hε hε1]
    exact hk
  have hnz' : ∀ j C, (D.shrinkRims ε hε hε1).vertex j ≠ .closedZero C := hnz
  refine ⟨(D.shrinkRims ε hε hε1).splitSphereInterval hσ' hv' hdisj, ⟨0, Nat.one_pos⟩, rfl,
    ?_, splitSphereInterval_ne_closedZero hσ' hv' hdisj hnz',
    fun hD => RimProduct.splitSphereInterval hσ' hv' hdisj (hrp hD)⟩
  exact (card_filter_badVertexSet_splitSphereInterval hσ' hv' hdisj hk').trans_eq
    (D.badVertexCount_shrinkRims ε hε hε1)

/-- The frozen form of N3a (`stub_N3a_split`), with its unused connectedness instance. -/
example [ConnectedSpace W.Carrier] (D : DecompositionCertificate W E)
    (hnz : ∀ k C, D.vertex k ≠ .closedZero C) (hσ : D.sphereSeamCount = 0)
    {k : Fin D.vertexCount} (hk : k ∈ D.badVertexSet)
    {P : PieceEmbedding W}
    {e : (ClosureSphere.{u} × Icc (0 : ℝ) 1) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1), 𝓡∂ 3⟯ P.Piece}
    (hv : D.vertex k = .slim P (.sphereInterval e)) :
    ∃ (D'' : DecompositionCertificate W E) (c'' : Fin D''.sphereSeamCount),
      D''.sphereSeamCount = 1 ∧
      (D''.badVertexSet.filter fun k => ∀ b, k ≠ D''.sphereSide c'' b).card + 1 ≤ D.badVertexCount ∧
      (∀ k C, D''.vertex k ≠ .closedZero C) ∧ (D.RimProduct → D''.RimProduct) :=
  D.exists_splitSphereInterval hnz hσ hk hv

/-- **Consumer: the dispatch without sphere seams.** With no sphere seam and positive measure,
either some bad vertex is a punctured `RP³` (the case of N2a), or the split of N3a exists. -/
theorem exists_puncturedRP3_or_splitSphereInterval (hnz : ∀ k C, D.vertex k ≠ .closedZero C)
    (hσ : D.sphereSeamCount = 0) (hμ : 0 < D.sphereMeasure) :
    (∃ k ∈ D.badVertexSet, ∃ (P : PieceEmbedding W)
      (c : OrientedBallChart projectiveThreeSpaceLift.{u}.toClosedOrientedManifold)
      (f : P.Piece → projectiveThreeSpaceLift.{u}.Carrier)
      (hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f)
      (hr : range f = {x | x ∉ c.chart '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1}),
      D.vertex k = .zero P (.puncturedRP3 c f hf hr)) ∨
    ∃ (D'' : DecompositionCertificate W E) (c'' : Fin D''.sphereSeamCount),
      D''.sphereSeamCount = 1 ∧
      (D''.badVertexSet.filter fun k => ∀ b, k ≠ D''.sphereSide c'' b).card + 1 ≤
        D.badVertexCount ∧
      (∀ k C, D''.vertex k ≠ .closedZero C) ∧ (D.RimProduct → D''.RimProduct) := by
  obtain ⟨k, hk, h | ⟨P, e, hv⟩⟩ := D.exists_bad_model_of_sphereMeasure_pos hσ hμ
  · exact Or.inl ⟨k, hk, h⟩
  · exact Or.inr (D.exists_splitSphereInterval hnz hσ hk hv)

end DecompositionCertificate

end GC.GraphManifold.Assembly
