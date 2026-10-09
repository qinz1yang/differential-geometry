import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyNormSplitSphereApplications
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereRecStep

/-!
# FC42 normalization, packet N3: the internal sphere cut at a bad `S² × I` vertex

Lane ASM-NRM3 (frozen statement `build-logs/scratch/ASM-NRM/Targets.lean` v2, N3). With no sphere
seam and no closed zero vertex, a bad vertex `k = .slim P (.sphereInterval e)` is split at its middle
sphere (N3a, `exists_splitSphereInterval`: one registered seam, non-side bad vertices at most
`b(D) - 1`); the strengthened recursion step S5 (`exists_sphereRecursionStep`) on that seam gives
one sphere cut of `W` whose capped components are Raw, `≅ RP³`, or carry a certificate with no sphere
seam (`σ < 1`), strictly fewer bad vertices than `D`, no closed zero vertex and the inherited
rim-product clause.

* `DecompositionCertificate.exists_internalSphereCut_sphereInterval` (**N3**, frozen text).
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

/-- **N3.** The internal sphere operation at a bad `S² × I` vertex (the middle sphere; the capped
carrier may have one or two components). -/
theorem exists_internalSphereCut_sphereInterval [ConnectedSpace W.Carrier]
    (hnz : ∀ k C, D.vertex k ≠ .closedZero C) (hσ : D.sphereSeamCount = 0)
    {k : Fin D.vertexCount} (hk : k ∈ D.badVertexSet) {P : PieceEmbedding W}
    {e : (ClosureSphere.{u} × Icc (0 : ℝ) 1) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1), 𝓡∂ 3⟯ P.Piece}
    (hv : D.vertex k = .slim P (.sphereInterval e)) :
    ∃ (S : SphereSeam W) (X : SphereCutCapped W S E) (DQ : X.Q.Components), ∀ i : Fin DQ.count,
      Nonempty (RawGraphPresentation (GC.Topology.componentCarrier X.Q DQ i)) ∨
      Nonempty ((GC.Topology.componentCarrier X.Q DQ i).Carrier ≃ₘ⟮
        (GC.Topology.componentCarrier X.Q DQ i).model, 𝓡 3⟯ projectiveThreeSpaceLift.{u}.Carrier) ∨
      ∃ D' : DecompositionCertificate (GC.Topology.componentCarrier X.Q DQ i) (X.componentTori DQ i),
        D'.sphereSeamCount = 0 ∧ D'.badVertexCount < D.badVertexCount ∧
        (∀ k C, D'.vertex k ≠ .closedZero C) ∧ (D.RimProduct → D'.RimProduct) := by
  obtain ⟨D'', c'', h1, hcount, hnz'', hrp⟩ := D.exists_splitSphereInterval hnz hσ hk hv
  obtain ⟨X, DQ, hX⟩ := D''.exists_sphereRecursionStep hnz'' c''
  refine ⟨D''.sphereSeam c'', X, DQ, fun i => ?_⟩
  rcases hX i with h | h | ⟨D', hσ', hb', hnz', hrp'⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨D', by omega, by omega, hnz', fun hD => hrp' (hrp hD)⟩)

end DecompositionCertificate

end GC.GraphManifold.Assembly
