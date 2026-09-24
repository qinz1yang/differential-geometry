import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.Metric.ScalarConvergence
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.Metric.CurveDistance
import DifferentialGeometry.Geometry.Compactness.SegmentTail
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.Metric.BallSystem.InverseCurves
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Chain
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.DirectedSubsequence.FiniteRadius
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.DirectedSubsequence.Tail
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.Construction

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Filter Set TopologicalSpace Bundle
open scoped _root_.Manifold ContDiff _root_.Topology NNReal ENNReal

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem exists_compact_eventually_inverse_curve_bound_of_finite_radius_chain
    (P : ∀ k, ProperMetricOn (I := I) (X.obj k)) (σ : ℕ → ℕ)
    {L : ℝ} (hL : 0 < L) (δ : ℕ → ℝ)
    (hδ : ∀ j, δ j ≤ (1 / 2 : ℝ) ^ (j + 1)) :
    letI : ∀ j, TopologicalSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).topology
    letI : ∀ j, ChartedSpace H (X.obj (σ j)).M := fun j => (X.obj (σ j)).charted
    letI : ∀ j, IsManifold I ∞ (X.obj (σ j)).M := fun j => (X.obj (σ j)).smooth
    letI : ∀ j, T2Space (X.obj (σ j)).M := fun j => (X.obj (σ j)).t2
    letI : ∀ j, SigmaCompactSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).sigmaCompact
    letI : ∀ j, MetricSpace (X.obj (σ j)).M := fun j =>
      ProperMetricOn.alignedMetricSpace (X.obj (σ j)) (P (σ j))
    ∀ Ψ : ∀ j, PartialDiffeomorph I I (X.obj (σ j)).M (X.obj (σ (j + 1))).M ∞,
    (∀ j, Ψ j (X.obj (σ j)).basepoint = (X.obj (σ (j + 1))).basepoint) →
    (∀ j, Nonempty (PartialDiffeomorphMetricApproximation (I := I)
      (Metric.closedBall (X.obj (σ j)).basepoint (finiteComparisonRadius L j)) (δ j) j
      (Ψ j) (X.obj (σ j)).metric (X.obj (σ (j + 1))).metric)) →
    ∀ N : ℕ, ∀ U : ∀ n, Opens (X.obj (σ (N + n))).M,
    ∀ hne : ∀ n, Nonempty (U n),
    letI := hne
    ∀ hU : ∀ n k, (U n : Set (X.obj (σ (N + n))).M) ⊆
      (chainComp (Mf := fun n => (X.obj (σ n)).M) (I := I) Ψ (N + n) k).source,
    ∀ hmap : ∀ n, (chainComp (Mf := fun n => (X.obj (σ n)).M) (I := I) Ψ (N + n) 1 : (X.obj (σ (N + n))).M →
        (X.obj (σ (N + (n + 1)))).M) '' (U n : Set (X.obj (σ (N + n))).M) ⊆
      (U (n + 1) : Set (X.obj (σ (N + (n + 1)))).M),
    (∀ n, Metric.ball (X.obj (σ (N + n))).basepoint (finiteStageRadius L (N + n)) ⊆
      (U n : Set (X.obj (σ (N + n))).M)) →
    ∀ gamma : ∀ m, ℝ → (X.obj (σ (N + m))).M,
    ∀ a b A : ℝ, ∀ C : ℝ≥0, A < L →
    (∀ᶠ m in atTop, LipschitzOnWith C (gamma m) (Icc a b)) →
    (∀ᶠ m in atTop, MapsTo (gamma m) (Icc a b)
      (Metric.ball (X.obj (σ (N + m))).basepoint A)) →
    let S := chainBallSystem (M := fun n => (X.obj (σ n)).M) (I := I) N U Ψ hU hmap
    ∀ G : SmoothRiemannianMetric I S.toSeqSystem.Lim,
      ∃ K : Set S.toSeqSystem.Lim, IsCompact K ∧ ∃ B : ℝ≥0, ∀ᶠ m in atTop,
        let Φ : PartialDiffeomorph I I S.toSeqSystem.Lim
            (X.obj (σ (N + m))).M ∞ :=
          PartialDiffeomorph.liftTargetOpen (S.inclPartialDiffeo m) rfl
        K ⊆ Φ.source ∧
        MapsTo ((Φ.symm : (X.obj (σ (N + m))).M → S.toSeqSystem.Lim) ∘ gamma m)
          (Icc a b) K ∧
          (∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
            riemannianEDistOf G (Φ.symm (gamma m s)) (Φ.symm (gamma m t)) ≤
              (B : ℝ≥0∞) * edist s t) ∧
          ∀ s ∈ Icc a b, Φ (Φ.symm (gamma m s)) = gamma m s := by
  classical
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : ∀ j, TopologicalSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).topology
  let : ∀ j, ChartedSpace H (X.obj (σ j)).M := fun j => (X.obj (σ j)).charted
  let : ∀ j, IsManifold I ∞ (X.obj (σ j)).M := fun j => (X.obj (σ j)).smooth
  let : ∀ j, T2Space (X.obj (σ j)).M := fun j => (X.obj (σ j)).t2
  let : ∀ j, SigmaCompactSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).sigmaCompact
  let : ∀ j, MetricSpace (X.obj (σ j)).M := fun j =>
      ProperMetricOn.alignedMetricSpace (X.obj (σ j)) (P (σ j))
  let : ∀ j, Bundle.RiemannianBundle
      (fun x : (X.obj (σ j)).M => TangentSpace I x) := fun j => (X.obj (σ j)).riemBundle
  have : ∀ j, IsRiemannianManifold I (X.obj (σ j)).M := fun j => by
    refine ⟨fun x y => ?_⟩
    have hreal := (P (σ j)).realizes x y
    rw [edist_dist, ← hreal]
    rfl
  have : ∀ j, ProperSpace (X.obj (σ j)).M := fun j => by
    have hmetric : ProperMetricOn.alignedMetricSpace (X.obj (σ j)) (P (σ j)) =
        (P (σ j)).ms := MetricSpace.replaceTopology_eq _ _
    change @ProperSpace _ (ProperMetricOn.alignedMetricSpace
      (X.obj (σ j)) (P (σ j))).toPseudoMetricSpace
    rw [hmetric]
    exact (P (σ j)).proper
  intro Ψ hbase hstep N U hne
  let := hne
  intro hU hmap hball gamma a b A C hAL hgamma hmem
  have hacc := chain_metric_approximation_on_finite_radii P σ hL δ hδ Ψ hbase hstep
  have hpow : Tendsto (fun n : ℕ => (3 / 4 : ℝ) ^ (N + n)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 3 / 4)
      (by norm_num : (3 / 4 : ℝ) < 1)).comp
      (by simpa only [Nat.add_comm] using tendsto_add_atTop_nat N)
  have hr : Tendsto (fun n => finiteStageRadius L (N + n)) atTop (𝓝 L) := by
    simpa only [finiteStageRadius, mul_zero, sub_zero] using
      (tendsto_const_nhds (x := L)).sub (hpow.const_mul (L / 2))
  apply exists_compact_eventually_inverse_curve_bound_of_eventual_metric_approximations
    (M := fun n => (X.obj (σ (N + n))).M) (I := I) U
    (fun n => chainComp Ψ (N + n) 1) (fun n => hU n 1) hmap
    (fun n => (X.obj (σ (N + n))).basepoint)
    (fun n => by exact hbase (N + n))
    (fun n => (X.obj (σ (N + n))).metric)
    (fun n => Geometry.Riemannian.isMetricNorm_of_riemannianBundle
      (I := I) (X.obj (σ (N + n))).metric)
    (fun n => finiteStageRadius L (N + n)) hr
    (Eventually.of_forall fun n => isCompact_closedBall _ _) (Eventually.of_forall hball) ?_
    gamma hAL hgamma hmem
  intro ε hε0 hε1
  obtain ⟨J, hJ⟩ := hacc ε hε0 hε1 0
  refine ⟨J, fun n hn k => ?_⟩
  have hs := nonempty_chain_metric_approximation_shift
    (M := fun n => (X.obj (σ n)).M) Ψ (fun n => (X.obj (σ n)).metric) N n k
    (hJ (N + n) (by omega) k)
  have hΨeq : (fun n => chainComp Ψ (N + n) 1) = (fun n => Ψ (N + n)) :=
    funext fun n => chainComp_one_eq Ψ (N + n)
  rw [hΨeq]
  exact hs

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem exists_compact_eventually_inverse_rescaled_segment_tail_bound
    (P : ∀ k, ProperMetricOn (I := I) (X.obj k)) (σ : ℕ → ℕ)
    {L : ℝ} (δ : ℕ → ℝ)
    (hδ : ∀ j, δ j ≤ (1 / 2 : ℝ) ^ (j + 1)) :
    letI : ∀ j, TopologicalSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).topology
    letI : ∀ j, ChartedSpace H (X.obj (σ j)).M := fun j => (X.obj (σ j)).charted
    letI : ∀ j, IsManifold I ∞ (X.obj (σ j)).M := fun j => (X.obj (σ j)).smooth
    letI : ∀ j, T2Space (X.obj (σ j)).M := fun j => (X.obj (σ j)).t2
    letI : ∀ j, SigmaCompactSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).sigmaCompact
    letI : ∀ j, MetricSpace (X.obj (σ j)).M := fun j =>
      ProperMetricOn.alignedMetricSpace (X.obj (σ j)) (P (σ j))
    ∀ Ψ : ∀ j, PartialDiffeomorph I I (X.obj (σ j)).M (X.obj (σ (j + 1))).M ∞,
    (∀ j, Ψ j (X.obj (σ j)).basepoint = (X.obj (σ (j + 1))).basepoint) →
    (∀ j, Nonempty (PartialDiffeomorphMetricApproximation (I := I)
      (Metric.closedBall (X.obj (σ j)).basepoint (finiteComparisonRadius L j)) (δ j) j
      (Ψ j) (X.obj (σ j)).metric (X.obj (σ (j + 1))).metric)) →
    ∀ N : ℕ, ∀ U : ∀ n, Opens (X.obj (σ (N + n))).M,
    ∀ hne : ∀ n, Nonempty (U n),
    letI := hne
    ∀ hU : ∀ n k, (U n : Set (X.obj (σ (N + n))).M) ⊆
      (chainComp (Mf := fun n => (X.obj (σ n)).M) (I := I) Ψ (N + n) k).source,
    ∀ hmap : ∀ n, (chainComp (Mf := fun n => (X.obj (σ n)).M) (I := I) Ψ (N + n) 1 : (X.obj (σ (N + n))).M →
        (X.obj (σ (N + (n + 1)))).M) '' (U n : Set (X.obj (σ (N + n))).M) ⊆
      (U (n + 1) : Set (X.obj (σ (N + (n + 1)))).M),
    (∀ n, Metric.ball (X.obj (σ (N + n))).basepoint (finiteStageRadius L (N + n)) ⊆
      (U n : Set (X.obj (σ (N + n))).M)) →
    ∀ gamma : ∀ m, ℝ → (X.obj (σ (N + m))).M,
    ∀ length start : ℕ → ℝ, ∀ ell : ℝ, 0 < ell →
    (∀ m, start m ∈ Icc 0 (length m)) →
    (∀ m, ∀ s ∈ Icc 0 (length m), ∀ t ∈ Icc 0 (length m),
      dist (gamma m s) (gamma m t) = |s - t|) →
    (∀ m, gamma m 0 = (X.obj (σ (N + m))).basepoint) →
    Tendsto length atTop (𝓝 L) →
    Tendsto (fun m => length m - start m) atTop (𝓝 ell) →
    ∀ T : ℝ, 0 ≤ T → T < ell →
    let S := chainBallSystem (M := fun n => (X.obj (σ n)).M) (I := I) N U Ψ hU hmap
    ∀ G : SmoothRiemannianMetric I S.toSeqSystem.Lim,
      ∃ K : Set S.toSeqSystem.Lim, IsCompact K ∧ ∃ B : ℝ≥0, ∀ᶠ m in atTop,
        let Φ : PartialDiffeomorph I I S.toSeqSystem.Lim
            (X.obj (σ (N + m))).M ∞ :=
          PartialDiffeomorph.liftTargetOpen (S.inclPartialDiffeo m) rfl
        K ⊆ Φ.source ∧
        MapsTo ((Φ.symm : (X.obj (σ (N + m))).M → S.toSeqSystem.Lim) ∘
          (fun s => gamma m (start m + (length m - start m) * s / ell)))
          (Icc (0 : ℝ) T) K ∧
          (∀ (s : ℝ), s ∈ Icc (0 : ℝ) T → ∀ (t : ℝ), t ∈ Icc (0 : ℝ) T →
            riemannianEDistOf G
                (Φ.symm (gamma m (start m + (length m - start m) * s / ell)))
                (Φ.symm (gamma m (start m + (length m - start m) * t / ell))) ≤
              (B : ℝ≥0∞) * edist s t) ∧
          ∀ (s : ℝ), s ∈ Icc (0 : ℝ) T →
            Φ (Φ.symm (gamma m (start m + (length m - start m) * s / ell))) =
              gamma m (start m + (length m - start m) * s / ell) := by
  classical
  let : ∀ j, TopologicalSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).topology
  let : ∀ j, ChartedSpace H (X.obj (σ j)).M := fun j => (X.obj (σ j)).charted
  let : ∀ j, IsManifold I ∞ (X.obj (σ j)).M := fun j => (X.obj (σ j)).smooth
  let : ∀ j, T2Space (X.obj (σ j)).M := fun j => (X.obj (σ j)).t2
  let : ∀ j, SigmaCompactSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).sigmaCompact
  let : ∀ j, MetricSpace (X.obj (σ j)).M := fun j =>
      ProperMetricOn.alignedMetricSpace (X.obj (σ j)) (P (σ j))
  intro Ψ hbase hstep N U hne
  let := hne
  intro hU hmap hball gamma length start ell hell hstart hsegment hzero hlength htail T hT hTell
  dsimp only
  intro G
  have hstartLim : Tendsto start atTop (𝓝 (L - ell)) := by
    simpa only [sub_sub_cancel] using hlength.sub htail
  have hnonneg : 0 ≤ L - ell :=
    ge_of_tendsto hstartLim (Eventually.of_forall fun m => (hstart m).1)
  have hL : 0 < L := by linarith
  obtain ⟨A, _hApos, hAL, hA⟩ :=
    Geometry.eventually_rescaled_segment_tail_subset_ball gamma length start hell
      hstart hsegment hlength htail hT hTell
  have hlip : ∀ᶠ m in atTop, LipschitzOnWith 2
      (fun s => gamma m (start m + (length m - start m) * s / ell)) (Icc (0 : ℝ) T) :=
    (Geometry.eventually_lipschitzOnWith_rescaled_segment_tail gamma length start hell
      hstart hsegment htail (C := 2) (by norm_num)).mono fun m hm =>
        hm.mono (Icc_subset_Icc_right hTell.le)
  have hmem : ∀ᶠ m in atTop, MapsTo
      (fun s => gamma m (start m + (length m - start m) * s / ell)) (Icc (0 : ℝ) T)
      (Metric.ball (X.obj (σ (N + m))).basepoint A) := by
    filter_upwards [hA] with m hm
    intro s hs
    simpa only [hzero m] using hm s hs
  exact exists_compact_eventually_inverse_curve_bound_of_finite_radius_chain
    P σ hL δ hδ Ψ hbase hstep N U hne hU hmap hball
    (fun m s => gamma m (start m + (length m - start m) * s / ell))
    0 T A 2 hAL hlip hmem G


attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem tendsto_dist_inverse_rescaled_segment_tail_of_finite_radius_chain
    (P : ∀ k, ProperMetricOn (I := I) (X.obj k)) (σ : ℕ → ℕ)
    {L : ℝ} (δ : ℕ → ℝ)
    (hδ : ∀ j, δ j ≤ (1 / 2 : ℝ) ^ (j + 1)) :
    letI : ∀ j, TopologicalSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).topology
    letI : ∀ j, ChartedSpace H (X.obj (σ j)).M := fun j => (X.obj (σ j)).charted
    letI : ∀ j, IsManifold I ∞ (X.obj (σ j)).M := fun j => (X.obj (σ j)).smooth
    letI : ∀ j, T2Space (X.obj (σ j)).M := fun j => (X.obj (σ j)).t2
    letI : ∀ j, SigmaCompactSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).sigmaCompact
    letI : ∀ j, MetricSpace (X.obj (σ j)).M := fun j =>
      ProperMetricOn.alignedMetricSpace (X.obj (σ j)) (P (σ j))
    ∀ Ψ : ∀ j, PartialDiffeomorph I I (X.obj (σ j)).M (X.obj (σ (j + 1))).M ∞,
    (∀ j, Ψ j (X.obj (σ j)).basepoint = (X.obj (σ (j + 1))).basepoint) →
    (∀ j, Nonempty (PartialDiffeomorphMetricApproximation (I := I)
      (Metric.closedBall (X.obj (σ j)).basepoint (finiteComparisonRadius L j)) (δ j) j
      (Ψ j) (X.obj (σ j)).metric (X.obj (σ (j + 1))).metric)) →
    ∀ N : ℕ, ∀ U : ∀ n, Opens (X.obj (σ (N + n))).M,
    ∀ hne : ∀ n, Nonempty (U n),
    letI := hne
    ∀ hU : ∀ n k, (U n : Set (X.obj (σ (N + n))).M) ⊆
      (chainComp (Mf := fun n => (X.obj (σ n)).M) (I := I) Ψ (N + n) k).source,
    ∀ hmap : ∀ n, (chainComp (Mf := fun n => (X.obj (σ n)).M) (I := I) Ψ (N + n) 1 : (X.obj (σ (N + n))).M →
        (X.obj (σ (N + (n + 1)))).M) '' (U n : Set (X.obj (σ (N + n))).M) ⊆
      (U (n + 1) : Set (X.obj (σ (N + (n + 1)))).M),
    (∀ n, Metric.ball (X.obj (σ (N + n))).basepoint (finiteStageRadius L (N + n)) ⊆
      (U n : Set (X.obj (σ (N + n))).M)) →
    ∀ gamma : ∀ m, ℝ → (X.obj (σ (N + m))).M,
    ∀ length start : ℕ → ℝ, ∀ ell : ℝ, 0 < ell →
    (∀ m, start m ∈ Icc 0 (length m)) →
    (∀ m, ∀ s ∈ Icc 0 (length m), ∀ t ∈ Icc 0 (length m),
      dist (gamma m s) (gamma m t) = |s - t|) →
    (∀ m, gamma m 0 = (X.obj (σ (N + m))).basepoint) →
    Tendsto length atTop (𝓝 L) →
    Tendsto (fun m => length m - start m) atTop (𝓝 ell) →
    let S := chainBallSystem (M := fun n => (X.obj (σ n)).M) (I := I) N U Ψ hU hmap
    ∀ gInf gRef : ∀ n, SmoothRiemannianMetric I (U n),
    ∀ hg : S.MetricCocycle gInf,
    ∀ hconnected : ConnectedSpace S.toSeqSystem.Lim,
    letI := hconnected
    let Ψtail := fun n => chainComp (Mf := fun n => (X.obj (σ n)).M) (I := I) Ψ (N + n) 1
    let hUtail := fun n k => subset_chainComp_source Ψtail
      (fun n => (U n : Set (X.obj (σ (N + n))).M)) (fun n => hU n 1)
      (fun n x hx => hmap n ⟨x, hx, rfl⟩) n k
    ∀ φ : ℕ → ℕ, StrictMono φ →
    (∀ j, ∀ K : Set (U j), IsCompact K → MetricCPConvergenceOn K 0
      (fun k => chainPullbackSeq Ψtail (fun n => (X.obj (σ (N + n))).metric)
        (U j) (hUtail j) (φ k - j)) (gInf j) (gRef j)) →
    letI : CompleteSpace E := FiniteDimensional.complete ℝ E
    letI : LocallyCompactSpace H := I.locallyCompactSpace
    letI : LocallyCompactSpace S.toSeqSystem.Lim :=
      ChartedSpace.locallyCompactSpace H S.toSeqSystem.Lim
    letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
      ⟨(S.limitMetric gInf hg).toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
      ⟨⟨(S.limitMetric gInf hg).inner, (S.limitMetric gInf hg).contMDiff.continuous,
        fun _ _ _ => rfl⟩⟩
    letI : MetricSpace S.toSeqSystem.Lim := Geometry.Riemannian.HopfRinow.riemMetricSpace (I := I)
    let Φ : ∀ k, PartialDiffeomorph I I S.toSeqSystem.Lim (X.obj (σ (N + k))).M ∞ :=
      fun k => PartialDiffeomorph.liftTargetOpen (S.inclPartialDiffeo k) rfl
    ∀ s ∈ Ico 0 ell, ∀ t ∈ Ico 0 ell,
      Tendsto (fun k => dist
        ((Φ (φ k)).symm (gamma (φ k) (start (φ k) + (length (φ k) - start (φ k)) * s / ell)))
        ((Φ (φ k)).symm (gamma (φ k) (start (φ k) + (length (φ k) - start (φ k)) * t / ell))))
        atTop (𝓝 |s - t|) := by
  classical
  let : ∀ j, TopologicalSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).topology
  let : ∀ j, ChartedSpace H (X.obj (σ j)).M := fun j => (X.obj (σ j)).charted
  let : ∀ j, IsManifold I ∞ (X.obj (σ j)).M := fun j => (X.obj (σ j)).smooth
  let : ∀ j, T2Space (X.obj (σ j)).M := fun j => (X.obj (σ j)).t2
  let : ∀ j, SigmaCompactSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).sigmaCompact
  let : ∀ j, MetricSpace (X.obj (σ j)).M := fun j =>
    ProperMetricOn.alignedMetricSpace (X.obj (σ j)) (P (σ j))
  let : ∀ j, RiemannianBundle (fun z : (X.obj (σ j)).M => TangentSpace I z) :=
    fun j => (X.obj (σ j)).riemBundle
  have : ∀ j, IsRiemannianManifold I (X.obj (σ j)).M := fun j => by
    refine ⟨fun x y => ?_⟩
    have hreal := (P (σ j)).realizes x y
    rw [edist_dist, ← hreal]
    rfl
  intro Ψ hbase hstep N U hne
  let := hne
  intro hU hmap hball gamma length start ell hell hstart hsegment hzero hlength htail
  dsimp only
  intro gInf gRef hg hconnected
  let : ConnectedSpace (chainBallSystem (M := fun n => (X.obj (σ n)).M) (I := I) N U Ψ hU hmap).toSeqSystem.Lim := hconnected
  intro φ hφ hconv
  let Ψtail := fun n => chainComp (Mf := fun n => (X.obj (σ n)).M) (I := I) Ψ (N + n) 1
  let hUtail := fun n k => subset_chainComp_source Ψtail
    (fun n => (U n : Set (X.obj (σ (N + n))).M)) (fun n => hU n 1)
    (fun n x hx => hmap n ⟨x, hx, rfl⟩) n k
  let S := chainBallSystem (M := fun n => (X.obj (σ n)).M) (I := I) N U Ψ hU hmap
  have : ConnectedSpace (SmoothSeqSystem.ofPartialDiffeomorphs U Ψtail
      (fun n => hU n 1) hmap).toSeqSystem.Lim := hconnected
  apply tendsto_dist_inverse_rescaled_segment_tail_of_chain_pullback_convergence
    U Ψtail (fun n => hU n 1) hmap hUtail
    (fun n => (X.obj (σ (N + n))).metric)
    (fun n => Geometry.Riemannian.isMetricNorm_of_riemannianBundle
      (X.obj (σ (N + n))).metric)
    gInf gRef hg φ hφ hconv gamma length start hell hstart hsegment htail
  intro T hT hTell
  obtain ⟨K, hK, B, hKmap⟩ := exists_compact_eventually_inverse_rescaled_segment_tail_bound
    P σ δ hδ Ψ hbase hstep N U hne hU hmap hball gamma length start ell hell
    hstart hsegment hzero hlength htail T hT hTell (S.limitMetric gInf hg)
  exact ⟨K, hK, hKmap.mono fun k hk => ⟨hk.1, hk.2.1, hk.2.2.2⟩⟩

omit [NeZero (Module.finrank ℝ E)] in
theorem tendsto_metricScalarAt_inverse_rescaled_segment_tail_sub_of_finite_radius_chain
    (P : ∀ k, ProperMetricOn (I := I) (X.obj k)) (σ : ℕ → ℕ)
    {L : ℝ} (δ : ℕ → ℝ)
    (hδ : ∀ j, δ j ≤ (1 / 2 : ℝ) ^ (j + 1)) :
    (show Prop from by
      letI : CompleteSpace E := FiniteDimensional.complete ℝ E
      letI : ∀ j, TopologicalSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).topology
      letI : ∀ j, ChartedSpace H (X.obj (σ j)).M := fun j => (X.obj (σ j)).charted
      letI : ∀ j, IsManifold I ∞ (X.obj (σ j)).M := fun j => (X.obj (σ j)).smooth
      letI : ∀ j, T2Space (X.obj (σ j)).M := fun j => (X.obj (σ j)).t2
      letI : ∀ j, SigmaCompactSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).sigmaCompact
      letI : ∀ j, MetricSpace (X.obj (σ j)).M := fun j =>
        ProperMetricOn.alignedMetricSpace (X.obj (σ j)) (P (σ j))
      exact ∀ Ψ : ∀ j, PartialDiffeomorph I I (X.obj (σ j)).M (X.obj (σ (j + 1))).M ∞,
    (∀ j, Ψ j (X.obj (σ j)).basepoint = (X.obj (σ (j + 1))).basepoint) →
    (∀ j, Nonempty (PartialDiffeomorphMetricApproximation (I := I)
      (Metric.closedBall (X.obj (σ j)).basepoint (finiteComparisonRadius L j)) (δ j) j
      (Ψ j) (X.obj (σ j)).metric (X.obj (σ (j + 1))).metric)) →
    ∀ N : ℕ, ∀ U : ∀ n, Opens (X.obj (σ (N + n))).M,
    ∀ hne : ∀ n, Nonempty (U n),
    letI := hne
    ∀ hU : ∀ n k, (U n : Set (X.obj (σ (N + n))).M) ⊆
      (chainComp (Mf := fun n => (X.obj (σ n)).M) (I := I) Ψ (N + n) k).source,
    ∀ hmap : ∀ n, (chainComp (Mf := fun n => (X.obj (σ n)).M) (I := I) Ψ (N + n) 1 : (X.obj (σ (N + n))).M →
        (X.obj (σ (N + (n + 1)))).M) '' (U n : Set (X.obj (σ (N + n))).M) ⊆
      (U (n + 1) : Set (X.obj (σ (N + (n + 1)))).M),
    (∀ n, Metric.ball (X.obj (σ (N + n))).basepoint (finiteStageRadius L (N + n)) ⊆
      (U n : Set (X.obj (σ (N + n))).M)) →
    ∀ gamma : ∀ m, ℝ → (X.obj (σ (N + m))).M,
    ∀ length start : ℕ → ℝ, ∀ ell : ℝ, 0 < ell →
    (∀ m, start m ∈ Icc 0 (length m)) →
    (∀ m, ∀ s ∈ Icc 0 (length m), ∀ t ∈ Icc 0 (length m),
      dist (gamma m s) (gamma m t) = |s - t|) →
    (∀ m, gamma m 0 = (X.obj (σ (N + m))).basepoint) →
    Tendsto length atTop (𝓝 L) →
    Tendsto (fun m => length m - start m) atTop (𝓝 ell) →
    let S := chainBallSystem (M := fun n => (X.obj (σ n)).M) (I := I) N U Ψ hU hmap
    ∀ gInf gRef : ∀ n, SmoothRiemannianMetric I (U n),
    ∀ hg : S.MetricCocycle gInf,
    let Ψtail := fun n => chainComp (Mf := fun n => (X.obj (σ n)).M) (I := I) Ψ (N + n) 1
    let hUtail := fun n k => subset_chainComp_source Ψtail
      (fun n => (U n : Set (X.obj (σ (N + n))).M)) (fun n => hU n 1)
      (fun n x hx => hmap n ⟨x, hx, rfl⟩) n k
    ∀ φ : ℕ → ℕ, StrictMono φ →
    (∀ j, ∀ K : Set (U j), IsCompact K → MetricCPConvergenceOn K 2
      (fun k => chainPullbackSeq Ψtail (fun n => (X.obj (σ (N + n))).metric)
        (U j) (hUtail j) (φ k - j)) (gInf j) (gRef j)) →
    let Φ : ∀ k, PartialDiffeomorph I I S.toSeqSystem.Lim (X.obj (σ (N + k))).M ∞ :=
      fun k => PartialDiffeomorph.liftTargetOpen (S.inclPartialDiffeo k) rfl
    ∀ s ∈ Ico 0 ell,
      Tendsto (fun k => Geometry.Curvature.metricScalarAt (I := I)
          (X.obj (σ (N + φ k))).metric
          (gamma (φ k) (start (φ k) + (length (φ k) - start (φ k)) * s / ell)) -
        Geometry.Curvature.metricScalarAt (I := I) (S.limitMetric gInf hg)
          ((Φ (φ k)).symm (gamma (φ k)
            (start (φ k) + (length (φ k) - start (φ k)) * s / ell))))
        atTop (𝓝 (0 : ℝ))) := by
  classical
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : ∀ j, TopologicalSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).topology
  let : ∀ j, ChartedSpace H (X.obj (σ j)).M := fun j => (X.obj (σ j)).charted
  let : ∀ j, IsManifold I ∞ (X.obj (σ j)).M := fun j => (X.obj (σ j)).smooth
  let : ∀ j, T2Space (X.obj (σ j)).M := fun j => (X.obj (σ j)).t2
  let : ∀ j, SigmaCompactSpace (X.obj (σ j)).M := fun j => (X.obj (σ j)).sigmaCompact
  let : ∀ j, MetricSpace (X.obj (σ j)).M := fun j =>
    ProperMetricOn.alignedMetricSpace (X.obj (σ j)) (P (σ j))
  dsimp only
  intro Ψ hbase hstep N U hne
  let := hne
  intro hU hmap hball gamma length start ell hell hstart hsegment hzero hlength htail
    gInf gRef hg φ hφ hconv
  let Ψtail := fun n => chainComp (Mf := fun n => (X.obj (σ n)).M) (I := I) Ψ (N + n) 1
  let hUtail := fun n k => subset_chainComp_source Ψtail
    (fun n => (U n : Set (X.obj (σ (N + n))).M)) (fun n => hU n 1)
    (fun n x hx => hmap n ⟨x, hx, rfl⟩) n k
  let S := chainBallSystem (M := fun n => (X.obj (σ n)).M) (I := I) N U Ψ hU hmap
  let : ∀ n, SigmaCompactSpace (U n) := fun n =>
    isSigmaCompact_iff_sigmaCompactSpace.mp (Geometry.isSigmaCompact_of_isOpen I (U n).isOpen)
  intro s hs
  apply tendsto_metricScalarAt_inverse_sub_of_chain_pullback_convergence
    U Ψtail (fun n => hU n 1) hmap hUtail
    (fun n => (X.obj (σ (N + n))).metric) gInf gRef hg φ hφ hconv
    (fun k => gamma (φ k) (start (φ k) + (length (φ k) - start (φ k)) * s / ell))
  obtain ⟨K, hK, B, htrap⟩ := exists_compact_eventually_inverse_rescaled_segment_tail_bound
    P σ δ hδ Ψ hbase hstep N U hne hU hmap hball gamma length start ell hell
    hstart hsegment hzero hlength htail s hs.1 hs.2 (S.limitMetric gInf hg)
  refine ⟨K, hK, ?_⟩
  filter_upwards [hφ.tendsto_atTop.eventually htrap] with k hk
  exact ⟨hk.2.1 ⟨hs.1, le_rfl⟩, hk.2.2.2 s ⟨hs.1, le_rfl⟩⟩

end CheegerGromovCompactness
end DifferentialGeometry
