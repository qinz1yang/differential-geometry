import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepDLimitMetrics
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCompactnessSubseq
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.WindowDataPullback

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

/-!
# Step D6 assembly

This module aligns the shrunk-tail convergence/completeness output with the
subsequence of the original pointed sequence and performs the final Step D
field assembly.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable [I.Boundaryless]
variable [NeZero (Module.finrank ℝ E)]

/-- The concrete convergence data use the restricted limit metric itself as
their seminorm reference metric. -/
private def HasCanonRef
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {Phi : PointedRiemannianCGMaps (I := I) X L subseq}
    (C : PointedRiemannianCGConverges (I := I) X L subseq Phi) : Prop :=
  forall k : Nat,
    let D := C.metrics.domain k
    letI : TopologicalSpace (MetricSourceDomain (I := I) Phi k) := D.topology
    letI : ChartedSpace H (MetricSourceDomain (I := I) Phi k) := D.charted
    letI : IsManifold I ∞ (MetricSourceDomain (I := I) Phi k) := D.smooth
    D.referenceMetric = D.limitMetric

/-- The two whole-source estimates retained by the concrete Step-D sidecar.
The tail is supplied by `D6ChainData.close`; the finite head requires the
relatively compact collar argument recorded at the assembly frontier below. -/
private def HasCanonBounds
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {Phi : PointedRiemannianCGMaps (I := I) X L subseq}
    (C : PointedRiemannianCGConverges (I := I) X L subseq Phi) : Prop :=
  (exists Crel : Real, 1 <= Crel ∧
    forall k : Nat,
      let D := C.metrics.domain k
      letI : TopologicalSpace (MetricSourceDomain (I := I) Phi k) := D.topology
      letI : ChartedSpace H (MetricSourceDomain (I := I) Phi k) := D.charted
      letI : IsManifold I ∞ (MetricSourceDomain (I := I) Phi k) := D.smooth
      MetricUniformEquivalentOn (I := I)
        (Set.univ : Set (MetricSourceDomain (I := I) Phi k))
        D.limitMetric D.pullbackMetric Crel) ∧
  (forall q : Nat, exists Cq : Real, 0 <= Cq ∧
    forall (k : Nat) (x : MetricSourceDomain (I := I) Phi k),
      let D := C.metrics.domain k
      letI : TopologicalSpace (MetricSourceDomain (I := I) Phi k) := D.topology
      letI : ChartedSpace H (MetricSourceDomain (I := I) Phi k) := D.charted
      letI : T2Space (MetricSourceDomain (I := I) Phi k) := D.t2
      letI : IsManifold I ∞ (MetricSourceDomain (I := I) Phi k) := D.smooth
      letI : SigmaCompactSpace (MetricSourceDomain (I := I) Phi k) := D.sigmaCompact
      metricCovDerivNorm (I := I) q D.pullbackMetric D.limitMetric x <= Cq)

private structure D6ChainData
    {M : ℕ → Type u} [∀ j, MetricSpace (M j)] [∀ j, ChartedSpace H (M j)]
    [∀ j, IsManifold I ∞ (M j)] [∀ j, SigmaCompactSpace (M j)] [∀ j, T2Space (M j)]
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (g : ∀ j, SmoothRiemannianMetric I (M j)) where
  start : ℕ
  one_le : 1 ≤ start
  zero : ∀ n k, BookApproxIsoPartialData (I := I)
    (Metric.closedBall (b (start + n)) ((2 : ℝ) ^ (start + n))) (1 / 2) 0
    (chainComp (I := I) (Mf := M) Ψ (start + n) k)
    (g (start + n)) (g ((start + n) + k))
  source : ∀ n k,
    (ballOpen b (fun s => (2 : ℝ) ^ s) (start + n) : Set (M (start + n))) ⊆
      (chainComp (I := I) (Mf := M) Ψ (start + n) k).source
  maps : ∀ n,
    (chainComp (I := I) (Mf := M) Ψ (start + n) 1 :
      M (start + n) → M (start + (n + 1))) ''
        (ballOpen b (fun s => (2 : ℝ) ^ s) (start + n) : Set (M (start + n))) ⊆
      (ballOpen b (fun s => (2 : ℝ) ^ s) (start + (n + 1)) :
        Set (M (start + (n + 1))))
  metric : ∀ n, SmoothRiemannianMetric I
    (ballOpen b (fun s => (2 : ℝ) ^ s) (start + n))
  close : ∀ ε : ℝ, 0 < ε → ∀ p : ℕ, ∃ n₀ : ℕ,
    ∀ n : ℕ, n₀ ≤ n →
      letI : SigmaCompactSpace
          (ballOpen b (fun s => (2 : ℝ) ^ s) (start + n)) :=
        isSigmaCompact_iff_sigmaCompactSpace.mp
          (Geometry.isSigmaCompact_of_isOpen I
            (ballOpen b (fun s => (2 : ℝ) ^ s) (start + n)).isOpen)
      ∀ l q : ℕ, q ≤ p →
        ∀ x : ballOpen b (fun s => (2 : ℝ) ^ s) (start + n),
          metricDerivNorm (I := I) q
            (chainPullbackSeq (I := I) Ψ g
              (ballOpen b (fun s => (2 : ℝ) ^ s) (start + n)) (source n) l)
            (metric n) (metric n) x ≤ ε
  step : ∀ n,
    let F : ballOpen b (fun s => (2 : ℝ) ^ s) (start + n) →
        ballOpen b (fun s => (2 : ℝ) ^ s) (start + (n + 1)) :=
      PartialDiffeomorph.opensMap
        (chainComp (I := I) (Mf := M) Ψ (start + n) 1) (source n 1) (maps n)
    ∀ (x : ballOpen b (fun s => (2 : ℝ) ^ s) (start + n))
      (v w : TangentSpace I x),
      (metric n).inner x v w =
        (metric (n + 1)).inner (F x)
          (mfderiv I I F x v) (mfderiv I I F x w)

set_option linter.unusedSectionVars false in
/-- The all-tail comparison estimate restricted to the shrunk stage, with the
zeroth chain pullback rewritten as the ambient stage metric. -/
private theorem D6ChainData.tail_close
    {M : ℕ → Type u} [∀ j, MetricSpace (M j)] [∀ j, ChartedSpace H (M j)]
    [∀ j, IsManifold I ∞ (M j)] [∀ j, SigmaCompactSpace (M j)] [∀ j, T2Space (M j)]
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (D : D6ChainData (I := I) b Ψ g)
    [∀ n, SigmaCompactSpace (tailBallOpen b D.start n)] :
    ∀ ε : ℝ, 0 < ε → ∀ p : ℕ, ∃ n₀ : ℕ,
      ∀ n, n₀ ≤ n → ∀ q, q ≤ p → ∀ x : tailBallOpen b D.start n,
        metricDerivNorm (I := I) q
          ((g (D.start + n)).restrictOpen (I := I) (tailBallOpen b D.start n))
          (tailMetric (I := I) b D.start D.metric n)
          (tailMetric (I := I) b D.start D.metric n) x ≤ ε := by
  intro ε hε p
  obtain ⟨n₀, hn₀⟩ := D.close ε hε p
  refine ⟨n₀, fun n hn q hqp x => ?_⟩
  let U := ballOpen b (fun s => (2 : ℝ) ^ s) (D.start + n)
  let V := tailBallOpen b D.start n
  letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  letI : SigmaCompactSpace V := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I V.isOpen)
  let inc : V → U := TopologicalSpace.Opens.inclusion
    (tailBall_le_large b D.start n)
  have hbig := hn₀ n hn 0 q hqp (inc x)
  rw [chainPullback_zero (I := I) Ψ g U (D.source n)] at hbig
  calc
    metricDerivNorm (I := I) q
        ((g (D.start + n)).restrictOpen (I := I) V)
        (tailMetric (I := I) b D.start D.metric n)
        (tailMetric (I := I) b D.start D.metric n) x =
      metricDerivNorm (I := I) q
        ((g (D.start + n)).restrictOpen (I := I) U)
        (D.metric n) (D.metric n) (inc x) := by
          simpa only [U, V, inc, tailMetric,
            SmoothRiemannianMetric.restrictOpen_flat] using
            metricDerivNorm_flat (I := I) (tailBall_le_large b D.start n)
              ((g (D.start + n)).restrictOpen (I := I) U)
              (D.metric n) (D.metric n) q x
    _ ≤ ε := hbig

/-- The compact ambient closed ball that contains an entire shrunk tail stage
while remaining inside the corresponding large open stage. -/
private def tailCollar
    {M : ℕ → Type u} [∀ j, MetricSpace (M j)]
    (b : ∀ j, M j) (j₀ n : ℕ) :
    Set (ballOpen b (fun s => (2 : ℝ) ^ s) (j₀ + n)) :=
  {x | dist (x : M (j₀ + n)) (b (j₀ + n)) ≤ (2 : ℝ) ^ n}

set_option linter.unusedSectionVars false in
/-- The full-radius tail collar is compact by ambient properness; the positive
tail shift keeps its closed boundary inside the large open stage. -/
private theorem tailCollar_compact
    {M : ℕ → Type u} [∀ j, MetricSpace (M j)] [∀ j, ProperSpace (M j)]
    (b : ∀ j, M j) (j₀ n : ℕ) (hj₀ : 1 ≤ j₀) :
    IsCompact (tailCollar b j₀ n) := by
  rw [Subtype.isCompact_iff]
  have hpow : (2 : ℝ) ^ n < (2 : ℝ) ^ (j₀ + n) := by
    apply pow_lt_pow_right₀ one_lt_two
    omega
  have hval : Subtype.val '' tailCollar b j₀ n =
      Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ n) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [tailCollar, Set.mem_setOf_eq, Metric.mem_closedBall, dist_comm] using hx
    · intro hy
      have hy' : dist y (b (j₀ + n)) ≤ (2 : ℝ) ^ n := by
        simpa only [Metric.mem_closedBall, dist_comm] using hy
      refine ⟨⟨y, ?_⟩, ?_, rfl⟩
      · change dist y (b (j₀ + n)) < (2 : ℝ) ^ (j₀ + n)
        exact hy'.trans_lt hpow
      · exact hy'
  rw [hval]
  exact isCompact_closedBall _ _

/-- Every point of a shrunk tail stage belongs to its compact collar in the
large stage. -/
private theorem tailBall_mem
    {M : ℕ → Type u} [∀ j, MetricSpace (M j)]
    (b : ∀ j, M j) (j₀ n : ℕ) (x : tailBallOpen b j₀ n) :
    TopologicalSpace.Opens.inclusion (tailBall_le_large b j₀ n) x ∈
      tailCollar b j₀ n := by
  change dist (x : M (j₀ + n)) (b (j₀ + n)) ≤ (2 : ℝ) ^ n
  exact x.2.le

/-- Uniform target-stage metric equivalence and covariant bounds before they
are pulled back to the canonical direct-limit source domains. -/
private def HasStageBounds
    {M : ℕ → Type u} [∀ j, MetricSpace (M j)] [∀ j, ChartedSpace H (M j)]
    [∀ j, IsManifold I ∞ (M j)] [∀ j, SigmaCompactSpace (M j)] [∀ j, T2Space (M j)]
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (D : D6ChainData (I := I) b Ψ g)
    [∀ n, SigmaCompactSpace (tailBallOpen b D.start n)] : Prop :=
  (∃ Crel : ℝ, 1 ≤ Crel ∧ ∀ n : ℕ,
    MetricUniformEquivalentOn (I := I)
      (Set.univ : Set (tailBallOpen b D.start n))
      (tailMetric (I := I) b D.start D.metric n)
      ((g (D.start + n)).restrictOpen (I := I) (tailBallOpen b D.start n)) Crel) ∧
  (∀ q : ℕ, ∃ Cq : ℝ, 0 ≤ Cq ∧
    ∀ (n : ℕ) (x : tailBallOpen b D.start n),
      metricCovDerivNorm (I := I) q
        ((g (D.start + n)).restrictOpen (I := I) (tailBallOpen b D.start n))
        (tailMetric (I := I) b D.start D.metric n) x ≤ Cq)

@[reducible] private noncomputable def alignedMetric
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)} (k : ℕ)
    (P : ProperMetricOn (I := I) (X.obj k)) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    MetricSpace (X.obj k).M := by
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  exact P.ms.replaceTopology (ProperMetricOn.top_eq (X.obj k) P).symm

/-- Properness of the realized metric after replacing its bundled topology by
the definitionally aligned manifold topology. -/
private theorem alignedProper
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)} (k : ℕ)
    (P : ProperMetricOn (I := I) (X.obj k)) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : MetricSpace (X.obj k).M := alignedMetric (I := I) k P
    ProperSpace (X.obj k).M := by
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : MetricSpace (X.obj k).M := alignedMetric (I := I) k P
  constructor
  intro x r
  have hcompact :
      @IsCompact (X.obj k).M
        P.ms.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
        (letI : MetricSpace (X.obj k).M := P.ms
         Metric.closedBall x r) := by
    letI : MetricSpace (X.obj k).M := P.ms
    letI : ProperSpace (X.obj k).M := P.proper
    exact isCompact_closedBall x r
  rw [ProperMetricOn.top_eq (X.obj k) P] at hcompact
  exact hcompact

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Direct-limit comparison maps whose targets are the original pointed-sequence members. -/
noncomputable def tailMemberMaps
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (P : ∀ k, ProperMetricOn (I := I) (X.obj k)) (σ : ℕ → ℕ) :
    letI : ∀ j, TopologicalSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).topology
    letI : ∀ j, ChartedSpace H (X.obj (σ j)).M := fun j => (X.obj (σ j)).charted
    letI : ∀ j, IsManifold I ∞ (X.obj (σ j)).M := fun j => (X.obj (σ j)).smooth
    letI : ∀ j, T2Space (X.obj (σ j)).M := fun j => (X.obj (σ j)).t2
    letI : ∀ j, SigmaCompactSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).sigmaCompact
    letI : ∀ j, MetricSpace (X.obj (σ j)).M := fun j =>
      alignedMetric (I := I) (σ j) (P (σ j))
    letI : ∀ j, IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.obj (σ j)).M := fun j => by
      change IsManifold I ∞ (X.obj (σ j)).M
      infer_instance
    letI : ∀ j, Bundle.RiemannianBundle
        (fun x : (X.obj (σ j)).M => TangentSpace I x) :=
      fun j => (X.obj (σ j)).riemBundle
    letI : ∀ j, IsRiemannianManifold I (X.obj (σ j)).M := fun j => by
      refine ⟨fun x y => ?_⟩
      have hreal := (P (σ j)).realizes x y
      rw [edist_dist, ← hreal]
      rfl
    ∀ (Ψ : ∀ j, PartialDiffeomorph I I (X.obj (σ j)).M
        (X.obj (σ (j + 1))).M (∞ : WithTop ℕ∞))
      (hbase : ∀ j, (Ψ j : (X.obj (σ j)).M → (X.obj (σ (j + 1))).M)
        (X.obj (σ j)).basepoint = (X.obj (σ (j + 1))).basepoint)
      (j₀ : ℕ)
      (D₀ : ∀ n k, BookApproxIsoPartialData (I := I)
        (Metric.closedBall (X.obj (σ (j₀ + n))).basepoint ((2 : ℝ) ^ (j₀ + n)))
        (1 / 2) 0
        (chainComp (I := I) (Mf := fun j => (X.obj (σ j)).M) Ψ (j₀ + n) k)
        (X.obj (σ (j₀ + n))).metric (X.obj (σ ((j₀ + n) + k))).metric),
      let b := fun j => (X.obj (σ j)).basepoint
      let g := fun j => (X.obj (σ j)).metric
      letI : ∀ n, Nonempty (tailBallOpen b j₀ n) := fun n => tailBall_nonempty b j₀ n
      let S := tailBallSystem (I := I) b Ψ hbase g (by
        intro j x v
        simpa using
          (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
            (I := I) (g j) x v)) j₀ D₀
      letI : ∀ n, SigmaCompactSpace (tailBallOpen b j₀ n) := fun n =>
        isSigmaCompact_iff_sigmaCompactSpace.mp
          (Geometry.isSigmaCompact_of_isOpen I (tailBallOpen b j₀ n).isOpen)
      ∀ (gTail : ∀ n, SmoothRiemannianMetric I (tailBallOpen b j₀ n))
        (hgTail : S.MetricCocycle gTail),
        PointedRiemannianCGMaps (I := I) X
          (limitPointedCoc S (tailCenter b j₀ 0) gTail hgTail)
          (fun n => σ (j₀ + n)) := by
  letI : ∀ j, TopologicalSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).topology
  letI : ∀ j, ChartedSpace H (X.obj (σ j)).M := fun j => (X.obj (σ j)).charted
  letI : ∀ j, IsManifold I ∞ (X.obj (σ j)).M := fun j => (X.obj (σ j)).smooth
  letI : ∀ j, T2Space (X.obj (σ j)).M := fun j => (X.obj (σ j)).t2
  letI : ∀ j, SigmaCompactSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).sigmaCompact
  letI : ∀ j, MetricSpace (X.obj (σ j)).M := fun j =>
    alignedMetric (I := I) (σ j) (P (σ j))
  letI : ∀ j, IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.obj (σ j)).M := fun j => by
    change IsManifold I ∞ (X.obj (σ j)).M
    infer_instance
  letI : ∀ j, Bundle.RiemannianBundle
      (fun x : (X.obj (σ j)).M => TangentSpace I x) :=
    fun j => (X.obj (σ j)).riemBundle
  letI : ∀ j, IsRiemannianManifold I (X.obj (σ j)).M := fun j => by
    refine ⟨fun x y => ?_⟩
    have hreal := (P (σ j)).realizes x y
    rw [edist_dist, ← hreal]
    rfl
  intro Ψ hbase j₀ D₀
  let b := fun j => (X.obj (σ j)).basepoint
  let g := fun j => (X.obj (σ j)).metric
  letI : ∀ n, Nonempty (tailBallOpen b j₀ n) := fun n => tailBall_nonempty b j₀ n
  let S := tailBallSystem (I := I) b Ψ hbase g (by
    intro j x v
    simpa using
      (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) (g j) x v)) j₀ D₀
  letI : ∀ n, SigmaCompactSpace (tailBallOpen b j₀ n) := fun n =>
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I (tailBallOpen b j₀ n).isOpen)
  dsimp only
  intro gTail hgTail
  let Φ : ∀ n, PartialDiffeomorph I I S.toSeqSystem.Lim
      (X.obj (σ (j₀ + n))).M (∞ : WithTop ℕ∞) := fun n =>
    PartialDiffeomorph.liftTargetOpen (S.inclPartialDiffeo n) rfl
  refine
    { partialDiffeomorph := Φ
      source_exhausts := ?_
      base_mem := fun n => ?_
      basepoint_map := fun n => ?_ }
  · change ExhaustsByOpen (fun k => Set.range (S.toSeqSystem.incl k))
    exact rangeExhausts S
  · change S.toSeqSystem.incl 0 (tailCenter b j₀ 0) ∈
      Set.range (S.toSeqSystem.incl n)
    exact ⟨S.toSeqSystem.F (Nat.zero_le n) (tailCenter b j₀ 0),
      S.toSeqSystem.incl_comp (Nat.zero_le n) (tailCenter b j₀ 0)⟩
  · calc
      Φ n (S.toSeqSystem.incl 0 (tailCenter b j₀ 0)) =
          (S.toSeqSystem.F (Nat.zero_le n) (tailCenter b j₀ 0) :
            (X.obj (σ (j₀ + n))).M) :=
        congrArg Subtype.val
          (S.invIncl_incl_le (Nat.zero_le n) (tailCenter b j₀ 0))
      _ = (X.obj (σ (j₀ + n))).basepoint := by
        exact congrArg Subtype.val
          (tailCenter_map (I := I) b Ψ hbase g (by
            intro j x v
            simpa using
              (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
                (I := I) (g j) x v)) j₀ D₀ n)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Convergence of the repointed tail sequence transfers to the original
sequence once the lifted inclusions are known to hit its basepoints. -/
noncomputable def tailMemberConv
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (P : ∀ k, ProperMetricOn (I := I) (X.obj k)) (σ : ℕ → ℕ) :
    letI : ∀ j, TopologicalSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).topology
    letI : ∀ j, ChartedSpace H (X.obj (σ j)).M := fun j => (X.obj (σ j)).charted
    letI : ∀ j, IsManifold I ∞ (X.obj (σ j)).M := fun j => (X.obj (σ j)).smooth
    letI : ∀ j, T2Space (X.obj (σ j)).M := fun j => (X.obj (σ j)).t2
    letI : ∀ j, SigmaCompactSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).sigmaCompact
    letI : ∀ j, MetricSpace (X.obj (σ j)).M := fun j =>
      alignedMetric (I := I) (σ j) (P (σ j))
    letI : ∀ j, IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.obj (σ j)).M := fun j => by
      change IsManifold I ∞ (X.obj (σ j)).M
      infer_instance
    letI : ∀ j, Bundle.RiemannianBundle
        (fun x : (X.obj (σ j)).M => TangentSpace I x) :=
      fun j => (X.obj (σ j)).riemBundle
    letI : ∀ j, IsRiemannianManifold I (X.obj (σ j)).M := fun j => by
      refine ⟨fun x y => ?_⟩
      have hreal := (P (σ j)).realizes x y
      rw [edist_dist, ← hreal]
      rfl
    ∀ (Ψ : ∀ j, PartialDiffeomorph I I (X.obj (σ j)).M
        (X.obj (σ (j + 1))).M (∞ : WithTop ℕ∞))
      (hbase : ∀ j, (Ψ j : (X.obj (σ j)).M → (X.obj (σ (j + 1))).M)
        (X.obj (σ j)).basepoint = (X.obj (σ (j + 1))).basepoint)
      (j₀ : ℕ)
      (D₀ : ∀ n k, BookApproxIsoPartialData (I := I)
        (Metric.closedBall (X.obj (σ (j₀ + n))).basepoint ((2 : ℝ) ^ (j₀ + n)))
        (1 / 2) 0
        (chainComp (I := I) (Mf := fun j => (X.obj (σ j)).M) Ψ (j₀ + n) k)
        (X.obj (σ (j₀ + n))).metric (X.obj (σ ((j₀ + n) + k))).metric),
      let b := fun j => (X.obj (σ j)).basepoint
      let g := fun j => (X.obj (σ j)).metric
      letI : ∀ n, Nonempty (tailBallOpen b j₀ n) := fun n => tailBall_nonempty b j₀ n
      let S := tailBallSystem (I := I) b Ψ hbase g (by
        intro j x v
        simpa using
          (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
            (I := I) (g j) x v)) j₀ D₀
      letI : ∀ n, SigmaCompactSpace (tailBallOpen b j₀ n) := fun n =>
        isSigmaCompact_iff_sigmaCompactSpace.mp
          (Geometry.isSigmaCompact_of_isOpen I (tailBallOpen b j₀ n).isOpen)
      ∀ (gTail : ∀ n, SmoothRiemannianMetric I (tailBallOpen b j₀ n))
        (hgTail : S.MetricCocycle gTail),
        PointedRiemannianCGConverges (I := I)
            (chainAmbientSeq (I := I) j₀ (tailBallOpen b j₀) S
              (tailCenter b j₀ 0) g)
            (limitPointedCoc S (tailCenter b j₀ 0) gTail hgTail) id
            (chainAmbientMaps (I := I) j₀ (tailBallOpen b j₀) S
              (tailCenter b j₀ 0) g gTail hgTail) →
          PointedRiemannianCGConverges (I := I) X
            (limitPointedCoc S (tailCenter b j₀ 0) gTail hgTail)
            (fun n => σ (j₀ + n))
            (tailMemberMaps (I := I) P σ Ψ hbase j₀ D₀ gTail hgTail) := by
  letI : ∀ j, TopologicalSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).topology
  letI : ∀ j, ChartedSpace H (X.obj (σ j)).M := fun j => (X.obj (σ j)).charted
  letI : ∀ j, IsManifold I ∞ (X.obj (σ j)).M := fun j => (X.obj (σ j)).smooth
  letI : ∀ j, T2Space (X.obj (σ j)).M := fun j => (X.obj (σ j)).t2
  letI : ∀ j, SigmaCompactSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).sigmaCompact
  letI : ∀ j, MetricSpace (X.obj (σ j)).M := fun j =>
    alignedMetric (I := I) (σ j) (P (σ j))
  letI : ∀ j, IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.obj (σ j)).M := fun j => by
    change IsManifold I ∞ (X.obj (σ j)).M
    infer_instance
  letI : ∀ j, Bundle.RiemannianBundle
      (fun x : (X.obj (σ j)).M => TangentSpace I x) :=
    fun j => (X.obj (σ j)).riemBundle
  letI : ∀ j, IsRiemannianManifold I (X.obj (σ j)).M := fun j => by
    refine ⟨fun x y => ?_⟩
    have hreal := (P (σ j)).realizes x y
    rw [edist_dist, ← hreal]
    rfl
  intro Ψ hbase j₀ D₀
  let b := fun j => (X.obj (σ j)).basepoint
  let g := fun j => (X.obj (σ j)).metric
  letI : ∀ n, Nonempty (tailBallOpen b j₀ n) := fun n => tailBall_nonempty b j₀ n
  let S := tailBallSystem (I := I) b Ψ hbase g (by
    intro j x v
    simpa using
      (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) (g j) x v)) j₀ D₀
  letI : ∀ n, SigmaCompactSpace (tailBallOpen b j₀ n) := fun n =>
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I (tailBallOpen b j₀ n).isOpen)
  dsimp only
  intro gTail hgTail C
  let XTail := X.subseq (fun n => σ (j₀ + n))
  let bTail : ∀ n, (XTail.obj n).M := fun n =>
    (S.toSeqSystem.F (Nat.zero_le n) (tailCenter b j₀ 0) :
      (X.obj (σ (j₀ + n))).M)
  let L := limitPointedCoc S (tailCenter b j₀ 0) gTail hgTail
  let Φr : PointedRiemannianCGMaps (I := I) (XTail.repoint bTail) L id := by
    change PointedRiemannianCGMaps (I := I)
      (chainAmbientSeq (I := I) j₀ (tailBallOpen b j₀) S
        (tailCenter b j₀ 0) g) L id
    exact chainAmbientMaps (I := I) j₀ (tailBallOpen b j₀) S
      (tailCenter b j₀ 0) g gTail hgTail
  have hbase' : ∀ n,
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : TopologicalSpace (XTail.obj (id n)).M := (XTail.obj (id n)).topology
      letI : ChartedSpace H (XTail.obj (id n)).M := (XTail.obj (id n)).charted
      Φr.partialDiffeomorph n L.basepoint = (XTail.obj (id n)).basepoint := by
    intro n
    calc
      Φr.partialDiffeomorph n (S.toSeqSystem.incl 0 (tailCenter b j₀ 0)) =
          (S.toSeqSystem.F (Nat.zero_le n) (tailCenter b j₀ 0) :
            (X.obj (σ (j₀ + n))).M) :=
        congrArg Subtype.val
          (S.invIncl_incl_le (Nat.zero_le n) (tailCenter b j₀ 0))
      _ = (X.obj (σ (j₀ + n))).basepoint := by
        exact congrArg Subtype.val
          (tailCenter_map (I := I) b Ψ hbase g (by
            intro j x v
            simpa using
              (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
                (I := I) (g j) x v)) j₀ D₀ n)
  have Cr : PointedRiemannianCGConverges (I := I) (XTail.repoint bTail) L id Φr := by
    change PointedRiemannianCGConverges (I := I)
      (chainAmbientSeq (I := I) j₀ (tailBallOpen b j₀) S
        (tailCenter b j₀ 0) g) L id
      (chainAmbientMaps (I := I) j₀ (tailBallOpen b j₀) S
        (tailCenter b j₀ 0) g gTail hgTail)
    exact C
  have Cu := Cr.unrepoint bTail hbase'
  exact Cu.ofSubseq (fun n => σ (j₀ + n))

namespace StepDCanonData

/-- Sigma-compactness of a comparison map's canonical source open set. -/
noncomputable def canonSrc
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Phi : PointedRiemannianCGMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace L.M := L.topology
    IsSigmaCompact (Phi.source k) := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : SigmaCompactSpace L.M := L.sigmaCompact
  exact Geometry.isSigmaCompact_of_isOpen I (Phi.source_open k)

/-- Sigma-compactness of a comparison map's canonical target open set. -/
noncomputable def canonTgt
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Phi : PointedRiemannianCGMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace (X.obj (subseq k)).M := (X.obj (subseq k)).topology
    IsSigmaCompact (Phi.target k) := by
  letI : TopologicalSpace (X.obj (subseq k)).M := (X.obj (subseq k)).topology
  letI : ChartedSpace H (X.obj (subseq k)).M := (X.obj (subseq k)).charted
  letI : SigmaCompactSpace (X.obj (subseq k)).M := (X.obj (subseq k)).sigmaCompact
  exact Geometry.isSigmaCompact_of_isOpen I (Phi.target_open k)

/-- The restricted limit metric on the canonical source domain. -/
noncomputable def canonRef
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Phi : PointedRiemannianCGMaps (I := I) X L subseq) (k : Nat) :
    letI : TopologicalSpace (MetricSourceDomain (I := I) Phi k) :=
      metricSourceDomTop (I := I) Phi k
    letI : ChartedSpace H (MetricSourceDomain (I := I) Phi k) :=
      metricSourceDomCharted (I := I) Phi k
    letI : IsManifold I ∞ (MetricSourceDomain (I := I) Phi k) :=
      metricSourceDomSmooth (I := I) Phi k
    SmoothRiemannianMetric I (MetricSourceDomain (I := I) Phi k) := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : T2Space L.M := L.t2
  letI : IsManifold I ∞ L.M := L.smooth
  letI : SigmaCompactSpace L.M := L.sigmaCompact
  letI : TopologicalSpace (MetricSourceDomain (I := I) Phi k) :=
    metricSourceDomTop (I := I) Phi k
  letI : ChartedSpace H (MetricSourceDomain (I := I) Phi k) :=
    metricSourceDomCharted (I := I) Phi k
  letI : T2Space (MetricSourceDomain (I := I) Phi k) :=
    metricSourceDomT2 (I := I) Phi k
  letI : IsManifold I ∞ (MetricSourceDomain (I := I) Phi k) :=
    metricSourceDomSmooth (I := I) Phi k
  letI : SigmaCompactSpace (MetricSourceDomain (I := I) Phi k) :=
    metricSourceDomSigmaOf (I := I) Phi k (canonSrc (I := I) Phi k)
  exact L.metric.restrictOpen (I := I) (metricSourceOpen (I := I) Phi k)

/-- The canonical metric source data determined by comparison maps. -/
noncomputable def canonDomain
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Phi : PointedRiemannianCGMaps (I := I) X L subseq) (k : Nat) :
    MetricSourceData (I := I) Phi k :=
  MetricSourceData.ofRestrictPullback (I := I)
    (Φ := Phi) (k := k) (canonSrc (I := I) Phi k)
    (canonTgt (I := I) Phi k) (canonRef (I := I) Phi k)

end StepDCanonData

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
set_option linter.unusedSectionVars false in
/-- On a direct-limit stage source, the canonical restricted limit metric is
the pullback of the compatible stage metric by the source-target
diffeomorphism. -/
private theorem chain_canon_eq
    {M : ℕ → Type u} [∀ j, MetricSpace (M j)] [∀ j, ChartedSpace H (M j)]
    [∀ j, IsManifold I ∞ (M j)] [∀ j, SigmaCompactSpace (M j)] [∀ j, T2Space (M j)]
    (j₀ : ℕ) (U : ∀ n, TopologicalSpace.Opens (M (j₀ + n))) [∀ n, Nonempty (U n)]
    [∀ n, SigmaCompactSpace (U n)]
    (S : SmoothSeqSystem I (fun n => U n)) (O₀ : U 0)
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (gInf : ∀ n, SmoothRiemannianMetric I (U n))
    (hgInf : S.MetricCocycle gInf) (k : ℕ) :
    let Φ := chainAmbientMaps (I := I) j₀ U S O₀ g gInf hgInf
    let D := StepDCanonData.canonDomain (I := I) Φ k
    letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := D.topology
    letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) := D.charted
    letI : T2Space (MetricSourceDomain (I := I) Φ k) := D.t2
    letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) := D.smooth
    letI : SigmaCompactSpace (MetricSourceDomain (I := I) Φ k) := D.sigmaCompact
    D.limitMetric = Diffeomorph.pullbackMetric (I := I) (gInf k)
      (metricSourceTargetDiff (I := I) Φ k) := by
  let Φ := chainAmbientMaps (I := I) j₀ U S O₀ g gInf hgInf
  let D := StepDCanonData.canonDomain (I := I) Φ k
  letI : TopologicalSpace (limitPointedCoc S O₀ gInf hgInf).M :=
    (limitPointedCoc S O₀ gInf hgInf).topology
  letI : ChartedSpace H (limitPointedCoc S O₀ gInf hgInf).M :=
    (limitPointedCoc S O₀ gInf hgInf).charted
  letI : TopologicalSpace
      ((chainAmbientSeq (I := I) j₀ U S O₀ g).obj (id k)).M :=
    ((chainAmbientSeq (I := I) j₀ U S O₀ g).obj (id k)).topology
  letI : ChartedSpace H
      ((chainAmbientSeq (I := I) j₀ U S O₀ g).obj (id k)).M :=
    ((chainAmbientSeq (I := I) j₀ U S O₀ g).obj (id k)).charted
  letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) := D.topology
  letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) := D.charted
  letI : T2Space (MetricSourceDomain (I := I) Φ k) := D.t2
  letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) := D.smooth
  letI : SigmaCompactSpace (MetricSourceDomain (I := I) Φ k) := D.sigmaCompact
  letI : TopologicalSpace (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomTop (I := I) Φ k
  letI : ChartedSpace H (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomCharted (I := I) Φ k
  letI : T2Space (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomT2 (I := I) Φ k
  letI : IsManifold I ∞ (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomSmooth (I := I) Φ k
  letI : SigmaCompactSpace (MetricTargetDomain (I := I) Φ k) :=
    metricTargetDomSigmaOf (I := I) Φ k (StepDCanonData.canonTgt (I := I) Φ k)
  let F := metricSourceTargetDiff (I := I) Φ k
  have metric_ext : ∀ (g₁ g₂ : SmoothRiemannianMetric I
      (MetricSourceDomain (I := I) Φ k)),
      (∀ (x : MetricSourceDomain (I := I) Φ k) (v w : TangentSpace I x),
        g₁.inner x v w = g₂.inner x v w) → g₁ = g₂ := by
    intro g₁ g₂ h
    obtain ⟨i₁, s₁, p₁, b₁, c₁⟩ := g₁
    obtain ⟨i₂, s₂, p₂, b₂, c₂⟩ := g₂
    have hi : i₁ = i₂ :=
      funext fun x => ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun w => h x v w
    subst hi
    rfl
  apply metric_ext
  intro x v w
  change (S.limitMetric gInf hgInf).inner
      (x : (limitPointedCoc S O₀ gInf hgInf).M) v w =
    (gInf k).inner (F x : U k)
      (mfderiv I I F x v) (mfderiv I I F x w)
  rw [S.limitMetric_of_mem gInf hgInf k x.2]
  rw [metricSourceTargetDiff_mfderiv (I := I) Φ k x v,
    metricSourceTargetDiff_mfderiv (I := I) Φ k x w]
  let z : (limitPointedCoc S O₀ gInf hgInf).M := x
  have hxSource : z ∈ (S.inclPartialDiffeo k).source := by
    change z ∈ Set.range (S.toSeqSystem.incl k)
    exact x.2
  have hFx : (F x : U k) = Function.invFun (S.toSeqSystem.incl k) z := by
    apply Subtype.ext
    have hmapPoint : Φ.map k z =
        ((Function.invFun (S.toSeqSystem.incl k) z : U k) : M (j₀ + k)) := rfl
    exact (metricSourceTargetDiff_apply (I := I) Φ k x).trans hmapPoint
  have hmapv : mfderiv I I (Φ.map k) z v =
      mfderiv I I
        (S.inclPartialDiffeo k : (limitPointedCoc S O₀ gInf hgInf).M → U k)
        z v := by
    change mfderiv I I
      (PartialDiffeomorph.liftTargetOpen (S.inclPartialDiffeo k) rfl :
        (limitPointedCoc S O₀ gInf hgInf).M → M (j₀ + k)) z v = _
    exact PartialDiffeomorph.liftOpen_mfderiv
      (S.inclPartialDiffeo k) rfl hxSource v
  have hmapw : mfderiv I I (Φ.map k) z w =
      mfderiv I I
        (S.inclPartialDiffeo k : (limitPointedCoc S O₀ gInf hgInf).M → U k)
        z w := by
    change mfderiv I I
      (PartialDiffeomorph.liftTargetOpen (S.inclPartialDiffeo k) rfl :
        (limitPointedCoc S O₀ gInf hgInf).M → M (j₀ + k)) z w = _
    exact PartialDiffeomorph.liftOpen_mfderiv
      (S.inclPartialDiffeo k) rfl hxSource w
  rw [hFx, hmapv, hmapw]
  rfl

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
set_option linter.unusedSectionVars false in
/-- Covariant metric norms are unchanged by flat restriction to a smaller
ambient open carrier. -/
private theorem covFlat_eq
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    {U V : TopologicalSpace.Opens M} (hVU : V ≤ U)
    [SigmaCompactSpace U] [T2Space U] [SigmaCompactSpace V] [T2Space V]
    (h gRef : SmoothRiemannianMetric I U) (a : ℕ) (x : V) :
    metricCovDerivNorm (I := I) a
        (h.restrictOpenOfSubset (I := I) hVU)
        (gRef.restrictOpenOfSubset (I := I) hVU) x =
      metricCovDerivNorm (I := I) a h gRef
        (TopologicalSpace.Opens.inclusion hVU x) := by
  let W := nestedOpen hVU
  letI : SigmaCompactSpace W := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I W.isOpen)
  letI : IsManifold I 1 V := IsManifold.of_le (I := I) (M := V) (n := ∞) (by decide)
  letI : IsManifold I 2 V := IsManifold.of_le (I := I) (M := V) (n := ∞) (by decide)
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) V := by
    change IsManifold I ∞ V
    infer_instance
  letI : IsManifold I 1 W := IsManifold.of_le (I := I) (M := W) (n := ∞) (by decide)
  letI : IsManifold I 2 W := IsManifold.of_le (I := I) (M := W) (n := ∞) (by decide)
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) W := by
    change IsManifold I ∞ W
    infer_instance
  let F := flatNestedDiffeo (I := I) hVU
  rw [restrictSubset_pull (I := I) hVU h, restrictSubset_pull (I := I) hVU gRef]
  calc
    metricCovDerivNorm (I := I) a
        (Diffeomorph.pullbackMetric (I := I) (h.restrictOpen (I := I) W) F)
        (Diffeomorph.pullbackMetric (I := I) (gRef.restrictOpen (I := I) W) F) x =
      metricCovDerivNorm (I := I) a
        (h.restrictOpen (I := I) W) (gRef.restrictOpen (I := I) W) (F x) :=
      metricCovDerivNorm_pullback (I := I) a
        (h.restrictOpen (I := I) W) (gRef.restrictOpen (I := I) W) F x
    _ = metricCovDerivNorm (I := I) a h gRef ((F x : W) : U) :=
      covNorm_restrictOpen (I := I) h gRef W a (F x)
    _ = metricCovDerivNorm (I := I) a h gRef
        (TopologicalSpace.Opens.inclusion hVU x) := by rfl

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
set_option linter.unusedSectionVars false in
/-- The concrete all-tail estimate and compact finite head give one set of
whole-stage constants, uniform in the stage index. -/
private theorem D6ChainData.stage_bounds
    {M : ℕ → Type u} [∀ j, MetricSpace (M j)] [∀ j, ChartedSpace H (M j)]
    [∀ j, IsManifold I ∞ (M j)] [∀ j, SigmaCompactSpace (M j)] [∀ j, T2Space (M j)]
    [∀ j, ProperSpace (M j)]
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (D : D6ChainData (I := I) b Ψ g)
    [∀ n, SigmaCompactSpace (tailBallOpen b D.start n)] :
    HasStageBounds (I := I) b Ψ g D := by
  classical
  constructor
  · set dim : ℝ := (Module.finrank ℝ E : ℝ) with hdim
    have hdim0 : 0 ≤ dim := by rw [hdim]; positivity
    set ε₀ : ℝ := 1 / (2 * dim + 2) with hε₀
    have hε₀pos : 0 < ε₀ := by rw [hε₀]; positivity
    obtain ⟨n₀, hn₀⟩ := D.tail_close b Ψ g ε₀ hε₀pos 0
    have htail : ∀ n, n₀ ≤ n →
        MetricUniformEquivalentOn (I := I)
          (Set.univ : Set (tailBallOpen b D.start n))
          (tailMetric (I := I) b D.start D.metric n)
          ((g (D.start + n)).restrictOpen (I := I) (tailBallOpen b D.start n)) 2 := by
      intro n hn
      have htwo : (2 : ℝ) = (1 - (1 / 2 : ℝ))⁻¹ := by norm_num
      rw [htwo]
      refine metricUniformEquivalentOn_of_metricDerivNorm
        ((g (D.start + n)).restrictOpen (I := I) (tailBallOpen b D.start n))
        (tailMetric (I := I) b D.start D.metric n) (by norm_num) (by norm_num) ?_
      intro x _
      have hfr : (Module.finrank ℝ (TangentSpace I x) : ℝ) = dim := by
        rw [hdim]
        rfl
      rw [hfr]
      have hmd := hn₀ n hn 0 (le_refl 0) x
      calc
        dim * metricDerivNorm (I := I) 0
            ((g (D.start + n)).restrictOpen (I := I) (tailBallOpen b D.start n))
            (tailMetric (I := I) b D.start D.metric n)
            (tailMetric (I := I) b D.start D.metric n) x ≤ dim * ε₀ :=
          mul_le_mul_of_nonneg_left hmd hdim0
        _ ≤ 1 / 2 := by
          rw [hε₀, mul_one_div, div_le_iff₀ (by positivity)]
          nlinarith
    have hhead : ∀ n : ℕ, ∃ Cn : ℝ,
        MetricUniformEquivalentOn (I := I)
          (Set.univ : Set (tailBallOpen b D.start n))
          (tailMetric (I := I) b D.start D.metric n)
          ((g (D.start + n)).restrictOpen (I := I) (tailBallOpen b D.start n)) Cn := by
      intro n
      let U := ballOpen b (fun s => (2 : ℝ) ^ s) (D.start + n)
      let V := tailBallOpen b D.start n
      letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
        (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
      let inc : V → U := TopologicalSpace.Opens.inclusion
        (tailBall_le_large b D.start n)
      obtain ⟨Cn, hCn⟩ := equivOn_compact (I := I)
        (tailCollar_compact b D.start n D.one_le)
        (D.metric n) ((g (D.start + n)).restrictOpen (I := I) U)
      refine ⟨Cn, hCn.1, fun x _ v => ?_⟩
      have hx := hCn.2 (inc x) (tailBall_mem b D.start n x) v
      simpa only [U, V, inc, tailMetric,
        SmoothRiemannianMetric.restrictSubset_inner,
        SmoothRiemannianMetric.restrictOpen_inner] using hx
    choose Chead hChead using hhead
    have hChead0 : ∀ n, 0 ≤ Chead n := fun n =>
      le_trans zero_le_one (hChead n).1
    let Crel : ℝ := 2 + ∑ n ∈ Finset.range n₀, Chead n
    have hsum0 : 0 ≤ ∑ n ∈ Finset.range n₀, Chead n :=
      Finset.sum_nonneg fun n _ => hChead0 n
    refine ⟨Crel, by dsimp only [Crel]; linarith, fun n => ?_⟩
    by_cases hn : n₀ ≤ n
    · exact metricUniformEquivalentOn_of_le (htail n hn) (by
        dsimp only [Crel]
        linarith)
    · have hnlt : n < n₀ := Nat.lt_of_not_le hn
      refine metricUniformEquivalentOn_of_le (hChead n) ?_
      have hsingle : Chead n ≤ ∑ j ∈ Finset.range n₀, Chead j :=
        Finset.single_le_sum (fun j _ => hChead0 j) (Finset.mem_range.mpr hnlt)
      dsimp only [Crel]
      linarith
  · intro q
    obtain ⟨n₀, hn₀⟩ := D.tail_close b Ψ g 1 one_pos q
    set dim : ℝ := (Module.finrank ℝ E : ℝ) with hdim
    let Ctail : ℝ := Real.sqrt dim + 1
    have hsqrt0 : 0 ≤ Real.sqrt dim := Real.sqrt_nonneg _
    have hCtail0 : 0 ≤ Ctail := by
      dsimp only [Ctail]
      positivity
    have htail : ∀ n, n₀ ≤ n → ∀ x : tailBallOpen b D.start n,
        metricCovDerivNorm (I := I) q
          ((g (D.start + n)).restrictOpen (I := I) (tailBallOpen b D.start n))
          (tailMetric (I := I) b D.start D.metric n) x ≤ Ctail := by
      intro n hn x
      have hdiff := hn₀ n hn q (le_refl q) x
      refine (covNorm_le_add (I := I) q
        ((g (D.start + n)).restrictOpen (I := I) (tailBallOpen b D.start n))
        (tailMetric (I := I) b D.start D.metric n)
        (tailMetric (I := I) b D.start D.metric n) x).trans ?_
      cases q with
      | zero =>
          have hself := covNorm0_le (I := I)
            (tailMetric (I := I) b D.start D.metric n)
            (tailMetric (I := I) b D.start D.metric n) x
            (C := 1) (le_refl 1) (by
              intro v
              simp only [inv_one, one_mul]
              exact ⟨le_rfl, le_rfl⟩)
          rw [← hdim] at hself
          dsimp only [Ctail]
          linarith
      | succ a =>
          rw [covNorm_self_succ (I := I)]
          dsimp only [Ctail]
          linarith
    have hhead : ∀ n : ℕ, ∃ Cn : ℝ, 0 ≤ Cn ∧
        ∀ x : tailBallOpen b D.start n,
          metricCovDerivNorm (I := I) q
            ((g (D.start + n)).restrictOpen (I := I) (tailBallOpen b D.start n))
            (tailMetric (I := I) b D.start D.metric n) x ≤ Cn := by
      intro n
      let U := ballOpen b (fun s => (2 : ℝ) ^ s) (D.start + n)
      let V := tailBallOpen b D.start n
      letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
        (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
      let inc : V → U := TopologicalSpace.Opens.inclusion
        (tailBall_le_large b D.start n)
      obtain ⟨Cn, hCn⟩ := metricCovDerivNorm_bddOn (I := I)
        (tailCollar_compact b D.start n D.one_le) q
        ((g (D.start + n)).restrictOpen (I := I) U) (D.metric n)
      refine ⟨max 0 Cn, le_max_left _ _, fun x => ?_⟩
      have hflat := covFlat_eq (I := I) (tailBall_le_large b D.start n)
        ((g (D.start + n)).restrictOpen (I := I) U) (D.metric n) q x
      have heq :
          metricCovDerivNorm (I := I) q
              ((g (D.start + n)).restrictOpen (I := I) V)
              (tailMetric (I := I) b D.start D.metric n) x =
            metricCovDerivNorm (I := I) q
              ((g (D.start + n)).restrictOpen (I := I) U) (D.metric n) (inc x) := by
        simpa only [U, V, inc, tailMetric,
          SmoothRiemannianMetric.restrictOpen_flat] using hflat
      rw [heq]
      exact (hCn (inc x) (tailBall_mem b D.start n x)).trans (le_max_right _ _)
    choose Chead hChead0 hChead using hhead
    let Cq : ℝ := Ctail + ∑ n ∈ Finset.range n₀, Chead n
    have hsum0 : 0 ≤ ∑ n ∈ Finset.range n₀, Chead n :=
      Finset.sum_nonneg fun n hn => hChead0 n
    refine ⟨Cq, by dsimp only [Cq]; linarith, fun n x => ?_⟩
    by_cases hn : n₀ ≤ n
    · exact (htail n hn x).trans (by
        dsimp only [Cq]
        linarith)
    · have hnlt : n < n₀ := Nat.lt_of_not_le hn
      have hsingle : Chead n ≤ ∑ j ∈ Finset.range n₀, Chead j :=
        Finset.single_le_sum (fun j _ => hChead0 j) (Finset.mem_range.mpr hnlt)
      exact (hChead n x).trans (by
        dsimp only [Cq]
        linarith)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Concrete Step-D output retaining the canonical reference-metric choice
made by the direct-limit convergence construction.  The public
`MetricCompactnessConclusion` deliberately forgets this provenance. -/
structure StepDCanonData
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  mc : MetricCompactnessConclusion (I := I) X
  domain_eq : forall k : Nat,
    mc.convergence.metrics.domain k = StepDCanonData.canonDomain (I := I) mc.maps k
  ref_eq : forall k : Nat,
    let D := mc.convergence.metrics.domain k
    letI : TopologicalSpace (MetricSourceDomain (I := I) mc.maps k) := D.topology
    letI : ChartedSpace H (MetricSourceDomain (I := I) mc.maps k) := D.charted
    letI : IsManifold I ∞ (MetricSourceDomain (I := I) mc.maps k) := D.smooth
    D.referenceMetric = D.limitMetric
  rel : exists Crel : Real, 1 <= Crel ∧
    forall k : Nat,
      let D := mc.convergence.metrics.domain k
      letI : TopologicalSpace (MetricSourceDomain (I := I) mc.maps k) := D.topology
      letI : ChartedSpace H (MetricSourceDomain (I := I) mc.maps k) := D.charted
      letI : IsManifold I ∞ (MetricSourceDomain (I := I) mc.maps k) := D.smooth
      MetricUniformEquivalentOn (I := I)
        (Set.univ : Set (MetricSourceDomain (I := I) mc.maps k))
        D.limitMetric D.pullbackMetric Crel
  init_cov : forall q : Nat, exists Cq : Real, 0 <= Cq ∧
    forall (k : Nat) (x : MetricSourceDomain (I := I) mc.maps k),
      let D := mc.convergence.metrics.domain k
      letI : TopologicalSpace (MetricSourceDomain (I := I) mc.maps k) := D.topology
      letI : ChartedSpace H (MetricSourceDomain (I := I) mc.maps k) := D.charted
      letI : T2Space (MetricSourceDomain (I := I) mc.maps k) := D.t2
      letI : IsManifold I ∞ (MetricSourceDomain (I := I) mc.maps k) := D.smooth
      letI : SigmaCompactSpace (MetricSourceDomain (I := I) mc.maps k) := D.sigmaCompact
      metricCovDerivNorm (I := I) q D.pullbackMetric D.limitMetric x <= Cq

namespace StepDCanonData

/-- Move canonical Step-D data from a sequence-level subsequence back to the
original sequence.  The source-domain metrics are rewrapped field by field, so
the canonical reference identity is preserved definitionally. -/
def ofSeqSubseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (f : Nat -> Nat) (hf : StrictMono f)
    (D : StepDCanonData (I := I) (X.subseq f)) :
    StepDCanonData (I := I) X where
  mc := D.mc.ofSeqSubseq f hf
  domain_eq := by
    intro k
    change MetricSourceData.ofSeqSubseq (I := I) f k
        (D.mc.convergence.metrics.domain k) =
      canonDomain (I := I) (D.mc.maps.ofSeqSubseq f) k
    rw [D.domain_eq k]
    rfl
  ref_eq := by
    intro k
    simpa only [MetricCompactnessConclusion.ofSeqSubseq,
      PointedRiemannianCGConverges.ofSeqSubseq,
      MetricCGConvergenceData.ofSeqSubseq,
      MetricSourceData.ofSeqSubseq] using D.ref_eq k
  rel := by
    obtain ⟨Crel, hCrel, hrel⟩ := D.rel
    refine ⟨Crel, hCrel, fun k => ?_⟩
    simpa only [MetricCompactnessConclusion.ofSeqSubseq,
      PointedRiemannianCGConverges.ofSeqSubseq,
      MetricCGConvergenceData.ofSeqSubseq,
      MetricSourceData.ofSeqSubseq] using hrel k
  init_cov := by
    intro q
    obtain ⟨Cq, hCq, hcov⟩ := D.init_cov q
    refine ⟨Cq, hCq, fun k x => ?_⟩
    simpa only [MetricCompactnessConclusion.ofSeqSubseq,
      PointedRiemannianCGConverges.ofSeqSubseq,
      MetricCGConvergenceData.ofSeqSubseq,
      MetricSourceData.ofSeqSubseq] using hcov k x

end StepDCanonData

set_option maxHeartbeats 800000 in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The complete Step D assembly from the honest B/C comparison-map package,
retaining the canonical reference-metric provenance used by its concrete
restrict/pullback convergence construction. -/
noncomputable def compactness_canon
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (P : ∀ k, ProperMetricOn (I := I) (X.obj k))
    (B : StepB1RawInput (X := X) P) :
    StepDCanonData (I := I) X := by
  classical
  let hdirectedEx := directed_of_b1 (I := I) P B
  let σ := Classical.choose hdirectedEx
  have hσpack := Classical.choose_spec hdirectedEx
  have hσ : StrictMono σ := hσpack.1
  have hdirected := hσpack.2
  letI : ∀ j, TopologicalSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).topology
  letI : ∀ j, ChartedSpace H (X.obj (σ j)).M := fun j => (X.obj (σ j)).charted
  letI : ∀ j, IsManifold I ∞ (X.obj (σ j)).M := fun j => (X.obj (σ j)).smooth
  letI : ∀ j, T2Space (X.obj (σ j)).M := fun j => (X.obj (σ j)).t2
  letI : ∀ j, SigmaCompactSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).sigmaCompact
  letI : ∀ j, MetricSpace (X.obj (σ j)).M := fun j => (P (σ j)).ms
  let Ψ := Classical.choose hdirected
  have hΨpack := Classical.choose_spec hdirected
  have hbase := hΨpack.1
  have hdata := hΨpack.2
  letI : ∀ j, MetricSpace (X.obj (σ j)).M := fun j =>
    alignedMetric (I := I) (σ j) (P (σ j))
  letI : ∀ j, IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.obj (σ j)).M := fun j => by
    change IsManifold I ∞ (X.obj (σ j)).M
    infer_instance
  letI : ∀ j, Bundle.RiemannianBundle
      (fun x : (X.obj (σ j)).M => TangentSpace I x) :=
    fun j => (X.obj (σ j)).riemBundle
  letI : ∀ j, IsRiemannianManifold I (X.obj (σ j)).M := fun j => by
    refine ⟨fun x y => ?_⟩
    have hreal := (P (σ j)).realizes x y
    rw [edist_dist, ← hreal]
    rfl
  letI : ∀ j, ProperSpace (X.obj (σ j)).M := fun j =>
    alignedProper (I := I) (σ j) (P (σ j))
  let b := fun j => (X.obj (σ j)).basepoint
  let g := fun j => (X.obj (σ j)).metric
  have hD : Nonempty (D6ChainData (I := I) b Ψ g) := by
    obtain ⟨j₀, hj₀, D₀, hU, hmap, _φ, _hφ, gInf, _hconv, hclose, hstep⟩ :=
      exists_limits_close (I := I) b Ψ hbase g (by
        intro j x v
        simpa using
          (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
            (I := I) (g j) x v)) hdata
    exact ⟨
      { start := j₀
        one_le := hj₀
        zero := D₀
        source := hU
        maps := hmap
        metric := gInf
        close := hclose
        step := hstep }⟩
  let D := Classical.choice hD
  let j₀ := D.start
  have hj₀ : 1 ≤ j₀ := D.one_le
  let D₀ := D.zero
  let hU := D.source
  let hmap := D.maps
  let gInf := D.metric
  have hclose := D.close
  have hstep := D.step
  letI : ∀ n, Nonempty (tailBallOpen b j₀ n) := fun n => tailBall_nonempty b j₀ n
  letI : ∀ n, SigmaCompactSpace (tailBallOpen b j₀ n) := fun n =>
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I (tailBallOpen b j₀ n).isOpen)
  let S := tailBallSystem (I := I) b Ψ hbase g (by
    intro j x v
    simpa using
      (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) (g j) x v)) j₀ D₀
  let gTail := tailMetric (I := I) b j₀ gInf
  let hgTail : S.MetricCocycle gTail :=
    tailMetricCocycle (I := I) b Ψ hbase g (by
      intro j x v
      simpa using
        (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) (g j) x v)) j₀ D₀ hU hmap gInf hstep
  let L := limitPointedCoc S (tailCenter b j₀ 0) gTail hgTail
  let maps := tailMemberMaps (I := I) P σ Ψ hbase j₀ D₀ gTail hgTail
  have hcomplete : MetricComplete (I := I) L := by
    exact tailLimitComplete (I := I) b Ψ hbase g (by
      intro j x v
      simpa using
        (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) (g j) x v)) j₀ hj₀ D₀
      hU hmap gInf hstep hclose
  let hchain := tailAmbientConv (I := I) b Ψ hbase g (by
    intro j x v
    simpa using
      (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
      (I := I) (g j) x v)) j₀ D₀
    hU hmap gInf hstep hclose
  have hchain_ref : HasCanonRef (I := I) hchain := by
    intro k
    simp only [hchain, tailAmbientConv, ambientCGConverges,
      PointedRiemannianCGConverges.ofRestrictPullback,
      MetricCGConvergenceData.ofRestrictPullback,
      MetricCGConvergenceData.of_derivNormSupOn,
      MetricSourceData.ofRestrictPullback, MetricSourceData.ofCanonical,
      limitPointedCoc, limitPointed]
  have hchain_domain : forall k : Nat,
      hchain.metrics.domain k =
        StepDCanonData.canonDomain (I := I)
          (chainAmbientMaps (I := I) j₀ (tailBallOpen b j₀) S
            (tailCenter b j₀ 0) g gTail hgTail) k := by
    intro k
    simp only [hchain, tailAmbientConv, ambientCGConverges,
      PointedRiemannianCGConverges.ofRestrictPullback,
      MetricCGConvergenceData.ofRestrictPullback,
      MetricCGConvergenceData.of_derivNormSupOn,
      StepDCanonData.canonDomain, StepDCanonData.canonRef,
      limitPointedCoc, limitPointed]
    rfl
  have hstage : HasStageBounds (I := I) b Ψ g D :=
    D.stage_bounds (I := I) b Ψ g
  have hchain_bounds : HasCanonBounds (I := I) hchain := by
    constructor
    · obtain ⟨Crel, hCrel, hrel⟩ := hstage.1
      refine ⟨Crel, hCrel, fun k => ?_⟩
      rw [hchain_domain k]
      let Φc := chainAmbientMaps (I := I) j₀ (tailBallOpen b j₀) S
        (tailCenter b j₀ 0) g gTail hgTail
      let Dc := StepDCanonData.canonDomain (I := I) Φc k
      letI : TopologicalSpace (MetricSourceDomain (I := I) Φc k) := Dc.topology
      letI : ChartedSpace H (MetricSourceDomain (I := I) Φc k) := Dc.charted
      letI : T2Space (MetricSourceDomain (I := I) Φc k) := Dc.t2
      letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φc k) := Dc.smooth
      letI : SigmaCompactSpace (MetricSourceDomain (I := I) Φc k) := Dc.sigmaCompact
      letI : TopologicalSpace (MetricTargetDomain (I := I) Φc k) :=
        metricTargetDomTop (I := I) Φc k
      letI : ChartedSpace H (MetricTargetDomain (I := I) Φc k) :=
        metricTargetDomCharted (I := I) Φc k
      letI : T2Space (MetricTargetDomain (I := I) Φc k) :=
        metricTargetDomT2 (I := I) Φc k
      letI : IsManifold I ∞ (MetricTargetDomain (I := I) Φc k) :=
        metricTargetDomSmooth (I := I) Φc k
      letI : SigmaCompactSpace (MetricTargetDomain (I := I) Φc k) :=
        metricTargetDomSigmaOf (I := I) Φc k
          (StepDCanonData.canonTgt (I := I) Φc k)
      let F := metricSourceTargetDiff (I := I) Φc k
      dsimp only
      rw [chain_canon_eq (I := I) j₀ (tailBallOpen b j₀) S
        (tailCenter b j₀ 0) g gTail hgTail k]
      change MetricUniformEquivalentOn (I := I) Set.univ
        (Diffeomorph.pullbackMetric (I := I) (gTail k) F)
        (Diffeomorph.pullbackMetric (I := I)
          ((g (j₀ + k)).restrictOpen (I := I) (tailBallOpen b j₀ k)) F) Crel
      exact metricUniformEquivalentOn_pullback (I := I)
        (Set.univ : Set (tailBallOpen b j₀ k)) (gTail k)
        ((g (j₀ + k)).restrictOpen (I := I) (tailBallOpen b j₀ k))
        Crel (hrel k) F (by simp)
    · intro q
      obtain ⟨Cq, hCq, hcov⟩ := hstage.2 q
      refine ⟨Cq, hCq, fun k x => ?_⟩
      rw [hchain_domain k]
      let Φc := chainAmbientMaps (I := I) j₀ (tailBallOpen b j₀) S
        (tailCenter b j₀ 0) g gTail hgTail
      let Dc := StepDCanonData.canonDomain (I := I) Φc k
      letI : TopologicalSpace (MetricSourceDomain (I := I) Φc k) := Dc.topology
      letI : ChartedSpace H (MetricSourceDomain (I := I) Φc k) := Dc.charted
      letI : T2Space (MetricSourceDomain (I := I) Φc k) := Dc.t2
      letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φc k) := Dc.smooth
      letI : SigmaCompactSpace (MetricSourceDomain (I := I) Φc k) := Dc.sigmaCompact
      letI : TopologicalSpace (MetricTargetDomain (I := I) Φc k) :=
        metricTargetDomTop (I := I) Φc k
      letI : ChartedSpace H (MetricTargetDomain (I := I) Φc k) :=
        metricTargetDomCharted (I := I) Φc k
      letI : T2Space (MetricTargetDomain (I := I) Φc k) :=
        metricTargetDomT2 (I := I) Φc k
      letI : IsManifold I ∞ (MetricTargetDomain (I := I) Φc k) :=
        metricTargetDomSmooth (I := I) Φc k
      letI : SigmaCompactSpace (MetricTargetDomain (I := I) Φc k) :=
        metricTargetDomSigmaOf (I := I) Φc k
          (StepDCanonData.canonTgt (I := I) Φc k)
      let F := metricSourceTargetDiff (I := I) Φc k
      dsimp only
      rw [chain_canon_eq (I := I) j₀ (tailBallOpen b j₀) S
        (tailCenter b j₀ 0) g gTail hgTail k]
      change metricCovDerivNorm (I := I) q
        (Diffeomorph.pullbackMetric (I := I)
          ((g (j₀ + k)).restrictOpen (I := I) (tailBallOpen b j₀ k)) F)
        (Diffeomorph.pullbackMetric (I := I) (gTail k) F) x ≤ Cq
      rw [metricCovDerivNorm_pullback (I := I) q
        ((g (j₀ + k)).restrictOpen (I := I) (tailBallOpen b j₀ k))
        (gTail k) F x]
      exact hcov k (F x)
  let XTail := X.subseq (fun n => σ (j₀ + n))
  let bTail : forall n, (XTail.obj n).M := fun n =>
    (S.toSeqSystem.F (Nat.zero_le n) (tailCenter b j₀ 0) :
      (X.obj (σ (j₀ + n))).M)
  let Φr : PointedRiemannianCGMaps (I := I) (XTail.repoint bTail) L id := by
    change PointedRiemannianCGMaps (I := I)
      (chainAmbientSeq (I := I) j₀ (tailBallOpen b j₀) S
        (tailCenter b j₀ 0) g) L id
    exact chainAmbientMaps (I := I) j₀ (tailBallOpen b j₀) S
      (tailCenter b j₀ 0) g gTail hgTail
  have hbase' : forall n,
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : TopologicalSpace (XTail.obj (id n)).M := (XTail.obj (id n)).topology
      letI : ChartedSpace H (XTail.obj (id n)).M := (XTail.obj (id n)).charted
      Φr.partialDiffeomorph n L.basepoint = (XTail.obj (id n)).basepoint := by
    intro n
    calc
      Φr.partialDiffeomorph n (S.toSeqSystem.incl 0 (tailCenter b j₀ 0)) =
          (S.toSeqSystem.F (Nat.zero_le n) (tailCenter b j₀ 0) :
            (X.obj (σ (j₀ + n))).M) :=
        congrArg Subtype.val
          (S.invIncl_incl_le (Nat.zero_le n) (tailCenter b j₀ 0))
      _ = (X.obj (σ (j₀ + n))).basepoint := by
        exact congrArg Subtype.val
          (tailCenter_map (I := I) b Ψ hbase g (by
            intro j x v
            simpa using
              (DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
                (I := I) (g j) x v)) j₀ D₀ n)
  let hconverges : PointedRiemannianCGConverges (I := I) X L
      (fun n => σ (j₀ + n)) maps :=
    tailMemberConv (I := I) P σ Ψ hbase j₀ D₀ gTail hgTail hchain
  have hconverges_ref : HasCanonRef (I := I) hconverges := by
    intro k
    simpa only [hconverges, tailMemberConv,
      PointedRiemannianCGConverges.unrepoint,
      MetricCGConvergenceData.unrepoint,
      PointedRiemannianCGConverges.ofSubseq,
      PointedRiemannianCGConverges.ofSeqSubseq,
      MetricCGConvergenceData.ofSubseq,
      MetricCGConvergenceData.ofSeqSubseq] using hchain_ref k
  have hconverges_domain : forall k : Nat,
      hconverges.metrics.domain k =
        StepDCanonData.canonDomain (I := I) maps k := by
    intro k
    change MetricSourceData.ofSubseq (I := I) (fun n => σ (j₀ + n)) k
        (MetricSourceData.unrepoint (I := I) bTail hbase' k
          (hchain.metrics.domain k)) =
      StepDCanonData.canonDomain (I := I) maps k
    rw [hchain_domain k]
    rfl
  let mc : MetricCompactnessConclusion (I := I) X :=
    { subseq := fun n => σ (j₀ + n)
      strictMono := fun _ _ hnm => hσ (Nat.add_lt_add_left hnm j₀)
      limit := L
      limit_complete := hcomplete
      maps := maps
      convergence := hconverges }
  have hbounds : HasCanonBounds (I := I) hconverges := by
    simpa only [hconverges, tailMemberConv,
      PointedRiemannianCGConverges.unrepoint,
      MetricCGConvergenceData.unrepoint,
      MetricSourceData.unrepoint,
      PointedRiemannianCGConverges.ofSubseq,
      PointedRiemannianCGConverges.ofSeqSubseq,
      MetricCGConvergenceData.ofSubseq,
      MetricCGConvergenceData.ofSeqSubseq,
      MetricSourceData.ofSubseq,
      MetricSourceData.ofSeqSubseq] using hchain_bounds
  refine { mc := mc, domain_eq := ?_, ref_eq := ?_, rel := ?_, init_cov := ?_ }
  · intro k
    exact hconverges_domain k
  · intro k
    exact hconverges_ref k
  · simpa only [mc] using hbounds.1
  · simpa only [mc] using hbounds.2

/-- The public Step-D conclusion, obtained by forgetting the concrete
reference-metric provenance retained by `compactness_canon`. -/
noncomputable def compactness_of_b1
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (P : ∀ k, ProperMetricOn (I := I) (X.obj k))
    (B : StepB1RawInput (X := X) P) :
    MetricCompactnessConclusion (I := I) X :=
  (compactness_canon (I := I) P B).mc

end HCGCompactness
end DifferentialGeometry
