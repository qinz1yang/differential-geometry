import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyNormSplitProjective
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyNormSphereCutInterval

/-!
# FC42 normalization, packet N2: the internal sphere cut at a bad punctured `ℝP³` vertex

Lane ASM-NRM4 (frozen statement `build-logs/scratch/ASM-NRM/Targets.lean` v2, N2). With no sphere
seam and no closed zero vertex, a bad vertex `k = .zero P (.puncturedRP3 c f hf hr)` is split along
the sphere of chart radius `1 + η` (N2a, `exists_splitPuncturedRP3`: one registered seam, non-side
bad vertices at most `b(D) - 1`); the strengthened recursion step S5 (`exists_sphereRecursionStep`)
on that seam gives one sphere cut of `W` whose capped components are Raw, `≅ ℝP³`, or carry a
certificate with no sphere seam (`σ < 1`), strictly fewer bad vertices than `D`, no closed zero
vertex and the inherited rim-product clause.

* `DecompositionCertificate.exists_internalSphereCut_puncturedRP3` (**N2**, frozen text);
* consumer `DecompositionCertificate.exists_internalSphereCut_of_sphereSeamCount_eq_zero`: with no
  sphere seam and positive measure, the internal sphere cut exists (N2 or N3 by the bad model).
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

/-- **N2.** The internal sphere operation at a bad punctured `ℝP³` vertex: one sphere cut of `W`
(the sphere parallel to the partitioned face, outside the missing ball), and for every capped
component: Raw, or `≅ ℝP³`, or a certificate with the canonical restricted ports, no sphere seam,
fewer bad vertices and no closed zero vertex. -/
theorem exists_internalSphereCut_puncturedRP3 [ConnectedSpace W.Carrier]
    (hnz : ∀ k C, D.vertex k ≠ .closedZero C) (hσ : D.sphereSeamCount = 0)
    {k : Fin D.vertexCount} (hk : k ∈ D.badVertexSet) {P : PieceEmbedding W}
    {c : OrientedBallChart projectiveThreeSpaceLift.{u}.toClosedOrientedManifold}
    {f : P.Piece → projectiveThreeSpaceLift.{u}.Carrier} {hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f}
    {hr : range f = {x | x ∉ c.chart '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1}}
    (hv : D.vertex k = .zero P (.puncturedRP3 c f hf hr)) :
    ∃ (S : SphereSeam W) (X : SphereCutCapped W S E) (DQ : X.Q.Components), ∀ i : Fin DQ.count,
      Nonempty (RawGraphPresentation (GC.Topology.componentCarrier X.Q DQ i)) ∨
      Nonempty ((GC.Topology.componentCarrier X.Q DQ i).Carrier ≃ₘ⟮
        (GC.Topology.componentCarrier X.Q DQ i).model, 𝓡 3⟯ projectiveThreeSpaceLift.{u}.Carrier) ∨
      ∃ D' : DecompositionCertificate (GC.Topology.componentCarrier X.Q DQ i)
          (X.componentTori DQ i),
        D'.sphereSeamCount = 0 ∧ D'.badVertexCount < D.badVertexCount ∧
        (∀ k C, D'.vertex k ≠ .closedZero C) ∧ (D.RimProduct → D'.RimProduct) := by
  obtain ⟨D'', c'', h1, hcount, hnz'', hrp⟩ := D.exists_splitPuncturedRP3 hnz hσ hk hv
  obtain ⟨X, DQ, hX⟩ := D''.exists_sphereRecursionStep hnz'' c''
  refine ⟨D''.sphereSeam c'', X, DQ, fun i => ?_⟩
  rcases hX i with h | h | ⟨D', hσ', hb', hnz', hrp'⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨D', by omega, by omega, hnz', fun hD => hrp' (hrp hD)⟩)

/-- **Consumer: the internal sphere cut without sphere seams.** With no sphere seam, no closed zero
vertex and positive measure, one sphere cut of `W` exists whose capped components are Raw, `≅ ℝP³`,
or carry a certificate with no sphere seam, fewer bad vertices and no closed zero vertex (N2 at a
bad punctured `ℝP³` vertex, N3 at a bad `S² × I` vertex). -/
theorem exists_internalSphereCut_of_sphereSeamCount_eq_zero [ConnectedSpace W.Carrier]
    (hnz : ∀ k C, D.vertex k ≠ .closedZero C) (hσ : D.sphereSeamCount = 0)
    (hμ : 0 < D.sphereMeasure) :
    ∃ (S : SphereSeam W) (X : SphereCutCapped W S E) (DQ : X.Q.Components), ∀ i : Fin DQ.count,
      Nonempty (RawGraphPresentation (GC.Topology.componentCarrier X.Q DQ i)) ∨
      Nonempty ((GC.Topology.componentCarrier X.Q DQ i).Carrier ≃ₘ⟮
        (GC.Topology.componentCarrier X.Q DQ i).model, 𝓡 3⟯ projectiveThreeSpaceLift.{u}.Carrier) ∨
      ∃ D' : DecompositionCertificate (GC.Topology.componentCarrier X.Q DQ i)
          (X.componentTori DQ i),
        D'.sphereSeamCount = 0 ∧ D'.badVertexCount < D.badVertexCount ∧
        (∀ k C, D'.vertex k ≠ .closedZero C) ∧ (D.RimProduct → D'.RimProduct) := by
  obtain ⟨k, hk, ⟨P, c, f, hf, hr, hv⟩ | ⟨P, e, hv⟩⟩ :=
    D.exists_bad_model_of_sphereMeasure_pos hσ hμ
  · exact D.exists_internalSphereCut_puncturedRP3 hnz hσ hk hv
  · exact D.exists_internalSphereCut_sphereInterval hnz hσ hk hv

end DecompositionCertificate

end GC.GraphManifold.Assembly
