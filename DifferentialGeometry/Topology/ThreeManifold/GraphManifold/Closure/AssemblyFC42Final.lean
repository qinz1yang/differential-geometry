import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyFC42FinalStep
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyRoundedRegionAssemblyTorusApplications
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyFC42ClosedPiecesApplications

/-!
# FC42 packet F1: the induction on `μ` and FC42 in form (b) (lane ASM-F1)

Review 40 item 1 (§1.5 / end of §2): closed zero vertex → the auxiliary `sec ≥ 0` disjunct; slim
vertex over the circle → Raw; `μ(D) = 0` → the torus assembly T4 with L1; `μ(D) > 0` → the sphere
step (`exists_sphereStep_of_steps`), the recursion on every inherited certificate, and the relative
COMPARE. Lead decision M1 (2026-10-04): FC42 is proved in form (b), with the rim-product clause
`hprod : D.RimProduct` of the input certificate as a plain hypothesis (it is consumed at `μ = 0`
by L1 and transported by every step); the frozen text over V4 certificates follows from the V5
field `rim_product` in one line (recorded in `build-logs/resume/state-ASM-F1.md`).

The packets not yet in the tree enter as plain hypotheses carrying their frozen texts:
* `hL1` — L1 `exists_solidTorus_of_ballHandleCycle_of_rimProduct` (lane ASM-L1b3);
* `hS5` — S5 `DecompositionCertificate.exists_sphereRecursionStep` (lane ASM-SPH2b);
* `hN2`, `hN3` — `DecompositionCertificate.exists_internalSphereCut_puncturedRP3`,
  `…_sphereInterval` (lane ASM-NRM3);
* `hA4`, `hA3` — `dry_L2_separating`, `dry_L2_nonseparating` (lane ASM-L2e2).

Main results: `nonempty_rawGraphPresentation_of_rimProduct_of_steps` (no closed zero vertex ⇒ Raw)
and `exists_rawGraphPresentation_or_aux_nonneg_of_certificate_of_rimProduct_of_steps` (FC42, form
(b)).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- **The μ-recursion of FC42** (form (b), packets as plain hypotheses): a certificate without
closed zero vertex whose rim charts satisfy the rim-product clause gives a raw presentation. -/
theorem nonempty_rawGraphPresentation_of_rimProduct_of_steps
    (hL1 : ∀ {W : CompactCarrier.{u}} (C : BallHandleCycle W), C.RimProduct →
      (∀ k, range (C.ball k).map ⊆ (W.interior : Set W.Carrier)) →
      Nonempty (solidTorusCarrier.{u}.Carrier ≃ₘ⟮solidTorusCarrier.{u}.model, 𝓡∂ 3⟯
        C.union.Piece))
    (hS5 : ∀ {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}
      (D : DecompositionCertificate W E) [ConnectedSpace W.Carrier],
      (∀ k C, D.vertex k ≠ .closedZero C) → ∀ c : Fin D.sphereSeamCount,
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
    (hN2 : ∀ {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}
      (D : DecompositionCertificate W E) [ConnectedSpace W.Carrier],
      (∀ k C, D.vertex k ≠ .closedZero C) → D.sphereSeamCount = 0 →
      ∀ {k : Fin D.vertexCount}, k ∈ D.badVertexSet →
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
    (hN3 : ∀ {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}
      (D : DecompositionCertificate W E) [ConnectedSpace W.Carrier],
      (∀ k C, D.vertex k ≠ .closedZero C) → D.sphereSeamCount = 0 →
      ∀ {k : Fin D.vertexCount}, k ∈ D.badVertexSet →
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
          (∀ k C, D'.vertex k ≠ .closedZero C) ∧ (D.RimProduct → D'.RimProduct))
    (hA4 : ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
      {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n}
      (X : SphereCutCapped W S E) (DQ : X.Q.Components), DQ.count = 2 →
      (∀ i, RawGraphPresentation (GC.Topology.componentCarrier X.Q DQ i)) →
      Nonempty (RawGraphPresentation W))
    (hA3 : ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
      {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n}
      (X : SphereCutCapped W S E) (DQ : X.Q.Components), DQ.count = 1 →
      (∀ i, RawGraphPresentation (GC.Topology.componentCarrier X.Q DQ i)) →
      Nonempty (RawGraphPresentation W))
    (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier] {n : ℕ} {E : BoundaryTori W n}
    (D : DecompositionCertificate W E) (hnz : ∀ k C, D.vertex k ≠ .closedZero C)
    (hprod : D.RimProduct) :
    Nonempty (RawGraphPresentation W) := by
  suffices h : ∀ (m : ℕ) (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier] {n : ℕ}
      {E : BoundaryTori W n} (D : DecompositionCertificate W E), D.sphereMeasure = m →
      (∀ k C, D.vertex k ≠ .closedZero C) → D.RimProduct → Nonempty (RawGraphPresentation W) from
    h _ W D rfl hnz hprod
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro W _ n E D hm hnz hprod
  -- a slim vertex over the circle (B2)
  by_cases hslim : ∃ (k : Fin D.vertexCount) (P : PieceEmbedding W) (p : P.Piece → Circle)
      (hp : ContMDiff (𝓡∂ 3) (𝓡 1) ∞ p) (hsub : ∀ q, Surjective (mfderiv (𝓡∂ 3) (𝓡 1) p q))
      (fib : SlimFibre P p) (hcl : (𝓡∂ 3).boundary P.Piece = ∅),
      D.vertex k = .slim P (.overCircle p hp hsub fib hcl)
  · exact D.nonempty_rawGraphPresentation_of_slimCircle hslim
  -- `μ = 0`: the torus assembly T4 with L1
  by_cases hμ : D.sphereMeasure = 0
  · exact D.nonempty_rawGraphPresentation_of_sphereMeasure_eq_zero_of_L1 hμ hnz hslim hprod
      fun C hpC hiC => hL1 C hpC hiC
  -- `μ > 0`: the sphere step, the recursion on each capped component, COMPARE
  obtain ⟨S, X, DQ, hX⟩ := D.exists_sphereStep_of_steps (Nat.pos_of_ne_zero hμ) (hS5 D hnz)
    (hN2 D hnz) (hN3 D hnz)
  refine X.nonempty_rawGraphPresentation_of_components DQ (hA3 W X DQ) (hA4 W X DQ) fun i => ?_
  have hQi : ConnectedSpace (GC.Topology.componentCarrier X.Q DQ i).Carrier := DQ.connected i
  rcases hX i with hR | hP | ⟨D', hlt, hz, hp⟩
  · exact hR
  · obtain ⟨e⟩ := hP
    exact nonempty_rawGraphPresentation_of_projectiveDiffeomorph _ e
  · exact ih _ (hm ▸ hlt) _ D' rfl hz (hp hprod)

/-- **FC42, form (b)** (lead decision M1): the frozen conclusion of
`exists_rawGraphPresentation_or_aux_nonneg_of_certificate` for a certificate satisfying the
rim-product clause, the packets not yet in the tree as plain hypotheses. A closed zero vertex gives
the auxiliary `sec ≥ 0` disjunct (B1); otherwise the μ-recursion gives Raw. -/
theorem exists_rawGraphPresentation_or_aux_nonneg_of_certificate_of_rimProduct_of_steps
    (hL1 : ∀ {W : CompactCarrier.{u}} (C : BallHandleCycle W), C.RimProduct →
      (∀ k, range (C.ball k).map ⊆ (W.interior : Set W.Carrier)) →
      Nonempty (solidTorusCarrier.{u}.Carrier ≃ₘ⟮solidTorusCarrier.{u}.model, 𝓡∂ 3⟯
        C.union.Piece))
    (hS5 : ∀ {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}
      (D : DecompositionCertificate W E) [ConnectedSpace W.Carrier],
      (∀ k C, D.vertex k ≠ .closedZero C) → ∀ c : Fin D.sphereSeamCount,
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
    (hN2 : ∀ {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}
      (D : DecompositionCertificate W E) [ConnectedSpace W.Carrier],
      (∀ k C, D.vertex k ≠ .closedZero C) → D.sphereSeamCount = 0 →
      ∀ {k : Fin D.vertexCount}, k ∈ D.badVertexSet →
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
    (hN3 : ∀ {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}
      (D : DecompositionCertificate W E) [ConnectedSpace W.Carrier],
      (∀ k C, D.vertex k ≠ .closedZero C) → D.sphereSeamCount = 0 →
      ∀ {k : Fin D.vertexCount}, k ∈ D.badVertexSet →
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
          (∀ k C, D'.vertex k ≠ .closedZero C) ∧ (D.RimProduct → D'.RimProduct))
    (hA4 : ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
      {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n}
      (X : SphereCutCapped W S E) (DQ : X.Q.Components), DQ.count = 2 →
      (∀ i, RawGraphPresentation (GC.Topology.componentCarrier X.Q DQ i)) →
      Nonempty (RawGraphPresentation W))
    (hA3 : ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
      {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n}
      (X : SphereCutCapped W S E) (DQ : X.Q.Components), DQ.count = 1 →
      (∀ i, RawGraphPresentation (GC.Topology.componentCarrier X.Q DQ i)) →
      Nonempty (RawGraphPresentation W))
    (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier] {n : ℕ} {E : BoundaryTori W n}
    (D : DecompositionCertificate W E) (hprod : D.RimProduct) :
    Nonempty (RawGraphPresentation W) ∨
      (W.model.boundary W.Carrier = ∅ ∧ ∃ g' : SmoothRiemannianMetric W.model W.Carrier,
        DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelow g' 0) := by
  by_cases hz : ∃ k C, D.vertex k = .closedZero C
  · exact Or.inr (D.boundary_eq_empty_and_exists_nonneg_of_closedZero hz)
  · exact Or.inl (nonempty_rawGraphPresentation_of_rimProduct_of_steps hL1 hS5 hN2 hN3 hA4 hA3 W D
      (fun k C h => hz ⟨k, C, h⟩) hprod)

end GC.GraphManifold.Assembly
