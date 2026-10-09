import
 DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopActualCertificate
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1CycleApplications
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCycleUnionApplications

/-!
The original one-ball/one-handle SAME certificate reaches FC42's zero-measure L1 branch.
The auxiliary deep solid core completes S³; the actual rim layer supplies every cycle's product.
-/
set_option autoImplicit false
noncomputable section
open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology
open GC.GraphManifold GC.Endpoint
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly.FC39P0.X137

local instance connectedLoopSource :
    ConnectedSpace (NoCuts.carrier standardThreeSphereLift.{0}).Carrier := inferInstance

theorem vertex_ne_closedZero (k : Fin loopActualCertificate.vertexCount)
    (C : ClosedZeroPiece (NoCuts.carrier standardThreeSphereLift.{0})) :
    loopActualCertificate.vertex k ≠ .closedZero C := by
  change Fin 2 at k
  fin_cases k <;> intro h <;> cases h

theorem not_slimOverCircle :
    ¬ ∃ (k : Fin loopActualCertificate.vertexCount)
      (P : PieceEmbedding (NoCuts.carrier standardThreeSphereLift.{0}))
      (p : P.Piece → Circle) (hp : ContMDiff (𝓡∂ 3) (𝓡 1) ∞ p)
      (hs : ∀ q, Surjective (mfderiv (𝓡∂ 3) (𝓡 1) p q))
      (fib : SlimFibre P p) (hc : (𝓡∂ 3).boundary P.Piece = ∅),
      loopActualCertificate.vertex k = .slim P (.overCircle p hp hs fib hc) := by
  rintro ⟨k, P, p, hp, hs, fib, hc, h⟩
  change Fin 2 at k
  fin_cases k <;> cases h

theorem badVertexCount_zero : loopActualCertificate.badVertexCount = 0 := by
  classical
  unfold DecompositionCertificate.badVertexCount
  rw [Finset.card_eq_zero]
  apply Finset.filter_eq_empty_iff.mpr
  intro k _ hk
  obtain ⟨hn, f, hf, _hkind, e, he⟩ := hk
  change Fin 2 at k
  change Fin 2 at f
  fin_cases f
  · change (0 : Fin 2) = k at hf
    subst k
    apply hn
    change loopBallVertexModel.IsBall
    exact ⟨_, _, rfl⟩
  · change loopCertificateFaceModel (1 : Fin 2) = Sum.inl e at he
    change Sum.inr loopComplementFaceModel = Sum.inl e at he
    cases he

theorem sphereMeasure_zero : loopActualCertificate.sphereMeasure = 0 := by
  rw [DecompositionCertificate.sphereMeasure, badVertexCount_zero,
    loopActualCertificate_noSeams.2.1]

theorem actual_cycle_L1 :
    ∃ P : loopActualCertificate.CyclePartition, 0 < P.cnt ∧
      ∀ j : Fin P.cnt,
        Nonempty (solidTorusCarrier.{0}.Carrier ≃ₘ⟮solidTorusCarrier.{0}.model, 𝓡∂ 3⟯
          (P.toBallHandleCycle j).union.Piece) := by
  obtain ⟨P⟩ := loopActualCertificate.nonempty_cyclePartition_of_badVertexCount_eq_zero
    loopActualCertificate_noSeams.2.1 badVertexCount_zero
  let h : Fin loopActualCertificate.handleCount := ⟨0, by change 0 < 1; norm_num⟩
  have hcnt : 0 < P.cnt := lt_of_le_of_lt (Nat.zero_le _) (P.handleIdx.symm h).1.isLt
  refine ⟨P, hcnt, ?_⟩
  intro j
  obtain ⟨_hu, hi, hr⟩ := P.toBallHandleCycle_spec loopActualCertificate_rimProduct j
  exact exists_solidTorus_of_ballHandleCycle_of_rimProduct (P.toBallHandleCycle j) hr hi

theorem raw_L1 : Nonempty (RawGraphPresentation
    (NoCuts.carrier standardThreeSphereLift.{0})) :=
  loopActualCertificate.nonempty_rawGraphPresentation_of_sphereMeasure_eq_zero
    sphereMeasure_zero vertex_ne_closedZero not_slimOverCircle loopActualCertificate_rimProduct

theorem strong_raw_or_aux_nonneg :
    Nonempty (RawGraphPresentation (NoCuts.carrier standardThreeSphereLift.{0})) ∨
      ((NoCuts.carrier standardThreeSphereLift.{0}).model.boundary
          (NoCuts.carrier standardThreeSphereLift.{0}).Carrier = ∅ ∧
        ∃ g : SmoothRiemannianMetric (NoCuts.carrier standardThreeSphereLift.{0}).model
            (NoCuts.carrier standardThreeSphereLift.{0}).Carrier,
          DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelow g 0) :=
  StrongCertificate.raw_or_aux_nonneg _ loopActualStrongCertificate

theorem fc42 :
    Nonempty (RawGraphPresentation (NoCuts.carrier standardThreeSphereLift.{0})) ∨
      ((NoCuts.carrier standardThreeSphereLift.{0}).model.boundary
          (NoCuts.carrier standardThreeSphereLift.{0}).Carrier = ∅ ∧
        ∃ g : SmoothRiemannianMetric (NoCuts.carrier standardThreeSphereLift.{0}).model
            (NoCuts.carrier standardThreeSphereLift.{0}).Carrier,
          DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelow g 0) :=
  exists_rawGraphPresentation_or_aux_nonneg_of_certificate_of_rimProduct _
    loopActualCertificate loopActualStrongCertificate.property

end GC.GraphManifold.Assembly.FC39P0.X137
