import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyNormBadModelsApplications
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereRecPortsApplications
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1WSideRimProduct
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.CarrierDiffeomorphTransport
import DifferentialGeometry.Geometry.Thurston.SphericalProductRawRecognition

/-!
# FC42 packet F1: the measure and the sphere step (lane ASM-F1)

Review 40 item 1 and the F1 row of its packet table; the lead decision M2 of 2026-10-04 (F1 owns the
sphere step, the case split seam / bad vertex of N4 (b)). The induction of FC42 runs on
`μ(D) = sphereSeamCount + badVertexCount` (`DecompositionCertificate.sphereMeasure`, lane ASM-NRM).

* Measure: `card_filter_badVertexSet_le`; `sphereMeasure_lt_of_sphereSeamCount_lt` (the seam
  branch: one seam fewer, bad vertices among the non-side bad vertices);
  `sphereMeasure_lt_of_badVertexCount_lt` (the internal-sphere branch: no seam before or after,
  fewer bad vertices).
* `exists_sphereStep_of_steps`: the sphere step (text of N4 (b)) for `μ(D) > 0` from the three
  packet outputs at `D` taken as plain hypotheses — S5 `exists_sphereRecursionStep` (lane
  ASM-SPH2b) at the seam `0` when there is a seam; otherwise the bad-vertex dispatch
  `exists_bad_model_of_sphereMeasure_pos` (built) and N2 `exists_internalSphereCut_puncturedRP3` or
  N3 `exists_internalSphereCut_sphereInterval` (lane ASM-NRM3).
* `nonempty_rawGraphPresentation_of_projectiveDiffeomorph`: a carrier diffeomorphic to `RP³` is
  Raw (the built raw presentation of `RP³` transported).
* `SphereCutCapped.nonempty_rawGraphPresentation_of_components`: Raw capped components give Raw `W`,
  through the relative COMPARE A3 (one component) / A4 (two components) as plain hypotheses (lane
  ASM-L2e2).
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

/-! ## The measure -/

/-- A filtered set of bad vertices has at most `badVertexCount` elements. -/
theorem card_filter_badVertexSet_le (p : Fin D.vertexCount → Prop) [DecidablePred p] :
    (D.badVertexSet.filter p).card ≤ D.badVertexCount := by
  rw [← D.card_badVertexSet]
  exact Finset.card_filter_le _ _

/-- **The seam branch decreases `μ`**: fewer sphere seams and the bad vertices among a filtered set
of bad vertices of `D`. -/
theorem sphereMeasure_lt_of_sphereSeamCount_lt {W' : CompactCarrier.{u}} {n' : ℕ}
    {E' : BoundaryTori W' n'} (D' : DecompositionCertificate W' E')
    (p : Fin D.vertexCount → Prop) [DecidablePred p]
    (hσ : D'.sphereSeamCount < D.sphereSeamCount)
    (hb : D'.badVertexCount ≤ (D.badVertexSet.filter p).card) :
    D'.sphereMeasure < D.sphereMeasure := by
  have := D.card_filter_badVertexSet_le p
  unfold sphereMeasure
  omega

/-- **The internal-sphere branch decreases `μ`**: no sphere seam before and after, fewer bad
vertices. -/
theorem sphereMeasure_lt_of_badVertexCount_lt {W' : CompactCarrier.{u}} {n' : ℕ}
    {E' : BoundaryTori W' n'} (D' : DecompositionCertificate W' E') (hσ : D.sphereSeamCount = 0)
    (hσ' : D'.sphereSeamCount = 0) (hb : D'.badVertexCount < D.badVertexCount) :
    D'.sphereMeasure < D.sphereMeasure := by
  unfold sphereMeasure
  omega

/-! ## The sphere step -/

/-- **The sphere step of FC42** (the text of N4 (b) `exists_sphereStep`, review 40 §1.5 / §2): for
`μ(D) > 0`, one sphere cut of `W` and, per capped component, Raw, `≅ RP³`, or an inherited
certificate with canonical restricted ports, strictly smaller `μ`, no closed zero vertex and the
rim-product clause transported. The packet outputs at `D` are plain hypotheses: `hS5` (S5 at every
registered seam), `hN2` / `hN3` (the internal sphere operations at a bad punctured `RP³` / `S² × I`
vertex when there is no seam). -/
theorem exists_sphereStep_of_steps (hμ : 0 < D.sphereMeasure)
    (hS5 : ∀ c : Fin D.sphereSeamCount,
      ∃ (X : SphereCutCapped W (D.sphereSeam c) E) (DQ : X.Q.Components), ∀ i : Fin DQ.count,
        Nonempty (RawGraphPresentation (GC.Topology.componentCarrier X.Q DQ i)) ∨
        Nonempty ((GC.Topology.componentCarrier X.Q DQ i).Carrier ≃ₘ⟮
          (GC.Topology.componentCarrier X.Q DQ i).model, 𝓡 3⟯ projectiveThreeSpaceLift.{u}.Carrier) ∨
        ∃ D' : DecompositionCertificate (GC.Topology.componentCarrier X.Q DQ i)
            (X.componentTori DQ i),
          D'.sphereSeamCount < D.sphereSeamCount ∧
          D'.badVertexCount ≤ (D.badVertexSet.filter fun k => ∀ b, k ≠ D.sphereSide c b).card ∧
          (∀ k C, D'.vertex k ≠ .closedZero C) ∧
          (D.RimProduct → D'.RimProduct))
    (hN2 : D.sphereSeamCount = 0 → ∀ {k : Fin D.vertexCount}, k ∈ D.badVertexSet →
      ∀ {P : PieceEmbedding W}
        {c : OrientedBallChart projectiveThreeSpaceLift.{u}.toClosedOrientedManifold}
        {f : P.Piece → projectiveThreeSpaceLift.{u}.Carrier}
        {hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f}
        {hr : range f = {x | x ∉ c.chart '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1}},
      D.vertex k = .zero P (.puncturedRP3 c f hf hr) →
      ∃ (S : SphereSeam W) (X : SphereCutCapped W S E) (DQ : X.Q.Components), ∀ i : Fin DQ.count,
        Nonempty (RawGraphPresentation (GC.Topology.componentCarrier X.Q DQ i)) ∨
        Nonempty ((GC.Topology.componentCarrier X.Q DQ i).Carrier ≃ₘ⟮
          (GC.Topology.componentCarrier X.Q DQ i).model, 𝓡 3⟯ projectiveThreeSpaceLift.{u}.Carrier) ∨
        ∃ D' : DecompositionCertificate (GC.Topology.componentCarrier X.Q DQ i)
            (X.componentTori DQ i),
          D'.sphereSeamCount = 0 ∧ D'.badVertexCount < D.badVertexCount ∧
          (∀ k C, D'.vertex k ≠ .closedZero C) ∧ (D.RimProduct → D'.RimProduct))
    (hN3 : D.sphereSeamCount = 0 → ∀ {k : Fin D.vertexCount}, k ∈ D.badVertexSet →
      ∀ {P : PieceEmbedding W}
        {e : (ClosureSphere.{u} × Icc (0 : ℝ) 1) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1), 𝓡∂ 3⟯ P.Piece},
      D.vertex k = .slim P (.sphereInterval e) →
      ∃ (S : SphereSeam W) (X : SphereCutCapped W S E) (DQ : X.Q.Components), ∀ i : Fin DQ.count,
        Nonempty (RawGraphPresentation (GC.Topology.componentCarrier X.Q DQ i)) ∨
        Nonempty ((GC.Topology.componentCarrier X.Q DQ i).Carrier ≃ₘ⟮
          (GC.Topology.componentCarrier X.Q DQ i).model, 𝓡 3⟯ projectiveThreeSpaceLift.{u}.Carrier) ∨
        ∃ D' : DecompositionCertificate (GC.Topology.componentCarrier X.Q DQ i)
            (X.componentTori DQ i),
          D'.sphereSeamCount = 0 ∧ D'.badVertexCount < D.badVertexCount ∧
          (∀ k C, D'.vertex k ≠ .closedZero C) ∧ (D.RimProduct → D'.RimProduct)) :
    ∃ (S : SphereSeam W) (X : SphereCutCapped W S E) (DQ : X.Q.Components), ∀ i : Fin DQ.count,
      Nonempty (RawGraphPresentation (GC.Topology.componentCarrier X.Q DQ i)) ∨
      Nonempty ((GC.Topology.componentCarrier X.Q DQ i).Carrier ≃ₘ⟮
        (GC.Topology.componentCarrier X.Q DQ i).model, 𝓡 3⟯ projectiveThreeSpaceLift.{u}.Carrier) ∨
      ∃ D' : DecompositionCertificate (GC.Topology.componentCarrier X.Q DQ i) (X.componentTori DQ i),
        D'.sphereMeasure < D.sphereMeasure ∧ (∀ k C, D'.vertex k ≠ .closedZero C) ∧
        (D.RimProduct → D'.RimProduct) := by
  by_cases hσ : 0 < D.sphereSeamCount
  · obtain ⟨X, DQ, hX⟩ := hS5 ⟨0, hσ⟩
    refine ⟨_, X, DQ, fun i => ?_⟩
    rcases hX i with h | h | ⟨D', hs, hb, hz, hp⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨D', D.sphereMeasure_lt_of_sphereSeamCount_lt D' _ hs hb, hz, hp⟩)
  · have hσ0 : D.sphereSeamCount = 0 := by omega
    obtain ⟨k, hk, ⟨P, c, f, hf, hr, hv⟩ | ⟨P, e, hv⟩⟩ :=
      D.exists_bad_model_of_sphereMeasure_pos hσ0 hμ
    · obtain ⟨S, X, DQ, hX⟩ := hN2 hσ0 hk hv
      refine ⟨S, X, DQ, fun i => ?_⟩
      rcases hX i with h | h | ⟨D', hs, hb, hz, hp⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨D', D.sphereMeasure_lt_of_badVertexCount_lt D' hσ0 hs hb, hz, hp⟩)
    · obtain ⟨S, X, DQ, hX⟩ := hN3 hσ0 hk hv
      refine ⟨S, X, DQ, fun i => ?_⟩
      rcases hX i with h | h | ⟨D', hs, hb, hz, hp⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨D', D.sphereMeasure_lt_of_badVertexCount_lt D' hσ0 hs hb, hz, hp⟩)

end DecompositionCertificate

/-! ## Raw capped components -/

/-- **An `RP³` component is Raw**: the built raw presentation of `projectiveThreeSpaceLift`
transported along the diffeomorphism. -/
theorem nonempty_rawGraphPresentation_of_projectiveDiffeomorph (X : CompactCarrier.{u})
    (e : X.Carrier ≃ₘ⟮X.model, 𝓡 3⟯ projectiveThreeSpaceLift.{u}.Carrier) :
    Nonempty (RawGraphPresentation X) := by
  obtain ⟨G⟩ := GC.GraphManifold.nonempty_rawGraphPresentation_projectiveThreeSpaceLift.{u}
  exact nonempty_rawGraphPresentation_of_carrierDiffeomorph G e.symm

/-- **Raw capped components give Raw `W`**: by the number of capped components (one or two,
`SphereCutCapped.components_count`), the non-separating COMPARE `hA3` or the separating COMPARE
`hA4` (plain hypotheses: the frozen A3 / A4 texts at this cut). -/
theorem SphereCutCapped.nonempty_rawGraphPresentation_of_components {W : CompactCarrier.{u}}
    [ConnectedSpace W.Carrier] {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n}
    (X : SphereCutCapped W S E) (DQ : X.Q.Components)
    (hA3 : DQ.count = 1 → (∀ i, RawGraphPresentation (GC.Topology.componentCarrier X.Q DQ i)) →
      Nonempty (RawGraphPresentation W))
    (hA4 : DQ.count = 2 → (∀ i, RawGraphPresentation (GC.Topology.componentCarrier X.Q DQ i)) →
      Nonempty (RawGraphPresentation W))
    (h : ∀ i, Nonempty (RawGraphPresentation (GC.Topology.componentCarrier X.Q DQ i))) :
    Nonempty (RawGraphPresentation W) := by
  rcases X.components_count DQ with h1 | h2
  · exact hA3 h1 fun i => (h i).some
  · exact hA4 h2 fun i => (h i).some

end GC.GraphManifold.Assembly
