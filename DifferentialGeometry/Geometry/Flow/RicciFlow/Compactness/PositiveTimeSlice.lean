import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.PositiveTimeUniform
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.PositiveTimeNoncollapsing
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Bounds.UniformInjectivityRadius
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.BoundedGeometryCanonical
import DifferentialGeometry.Geometry.Metric.Comparison.CompactBilipschitz

/-!
# Positive-time slices of curvature-controlled compact flows: bounded geometry (LFR50 part D)

Assembly of part D of the merged LFR50 design (§5). Let `F n : FlowTo (gSeq n) (τ n)` be Ricci
flows on one closed connected manifold `M` with `T < τ n` and `|Rm| ≤ B` on `[0, T]` (the part-B
output shape), and let the initial metrics have a common diameter bound `d₀` and a common
total-volume lower bound `v₀ > 0` (the part-A output). At `t* = T/2` the sequence
`X = pointedMetricSeq p (fun n => (F n).S.base.metric (T / 2))` satisfies every hypothesis of the
canonical bounded-geometry compactness supplier
`exists_canonical_metric_compactness_of_boundedGeometry`
(`Compactness/CheegerGromov/Pointed/Compactness/BoundedGeometryCanonical.lean`):

* `SeqMetricComplete X` (compact slices);
* every `X.obj i` is connected;
* `SeqBoundedGeometry X` with `C m = shiCompleteGlobalBound (dim M) m · B · (1/√(T/4) + √B)^m`
  (D2, `exists_uniform_positive_time_curvature_derivatives`);
* `BaseInjBound X` with one radius `ι > 0` (D3: diameter and volume at `T/2` from the flow
  comparisons, then Bishop–Gromov and the uniform Cheeger–Gromov–Taylor scale).

All constants depend only on `dim M`, `B`, `T`, `d₀`, `v₀` (and the order `m`), never on `n`.
`positiveTimeSlice_canonical_compactness_hypotheses_of_bilipschitz` takes the initial data in the
form part A produces it: the initial metrics uniformly bilipschitz to one fixed smooth metric.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [CompactSpace M] [BoundarylessManifold I M]

/-- **D4, the frozen §5 contract.** The time-`T/2` slices of a sequence of compact Ricci flows with
the part-B bounds and uniform initial diameter and volume bounds satisfy all hypotheses of the
canonical bounded-geometry compactness supplier, with constants independent of the index. -/
theorem positiveTimeSlice_canonical_compactness_hypotheses [ConnectedSpace M]
    (gSeq : ℕ → SmoothRiemannianMetric I M)
    (T B : ℝ) (hT : 0 < T) (hB : 0 < B)
    (τ : ℕ → ℝ) (hτ : ∀ n, T < τ n)
    (F : (n : ℕ) → FlowTo (I := I) (M := M) (gSeq n) (τ n))
    (hcurv : ∀ n t, t ∈ Icc 0 T → ∀ x : M,
      Real.sqrt (DifferentialGeometry.Tensor0SBundle.normSq0S
        ((F n).S.base.metric t) x 4
        (metricRm04 ((F n).S.base.metric t) x)) ≤ B)
    {d₀ v₀ : ℝ} (hv₀ : 0 < v₀)
    (hdiam : ∀ n x y, riemannianEDistOf (gSeq n) x y ≤ ENNReal.ofReal d₀)
    (hvol : ∀ n, ENNReal.ofReal v₀ ≤ riemannianVolumeMeasure I M (gSeq n) Set.univ)
    (p : M) :
    SeqMetricComplete (I := I) (pointedMetricSeq p fun n => (F n).S.base.metric (T / 2)) ∧
      (∀ i : ℕ,
        let _ : TopologicalSpace
            ((pointedMetricSeq p fun n => (F n).S.base.metric (T / 2)).obj i).M :=
          ((pointedMetricSeq p fun n => (F n).S.base.metric (T / 2)).obj i).topology
        ConnectedSpace ((pointedMetricSeq p fun n => (F n).S.base.metric (T / 2)).obj i).M) ∧
      Nonempty (SeqBoundedGeometry (I := I)
        (pointedMetricSeq p fun n => (F n).S.base.metric (T / 2))) ∧
      Nonempty (BaseInjBound (I := I)
        (pointedMetricSeq p fun n => (F n).S.base.metric (T / 2))) := by
  have hhalf : T / 2 ∈ Icc 0 T := ⟨by positivity, by linarith⟩
  have hhalf' : T / 2 ∈ Icc (T / 2) T := ⟨le_rfl, by linarith⟩
  refine ⟨⟨fun i => (RiemannianMetricComplete.of_compact (I := I)
      ((F i).S.base.metric (T / 2))).complete⟩, fun i => ‹ConnectedSpace M›, ?_, ?_⟩
  · obtain ⟨A, hA0, hA⟩ :=
      exists_uniform_positive_time_curvature_derivatives gSeq T B hT hB τ hτ F hcurv
    exact ⟨{ C := A
             nonneg := hA0
             bound := fun i k x => hA k i (T / 2) hhalf' x }⟩
  · let dstar : ℝ :=
      Real.exp ((Module.finrank ℝ E : ℝ) ^ 2 * B * (T / 2)) * (max d₀ 0 + 1)
    let vstar : ℝ := v₀ * Real.exp (-((Module.finrank ℝ E : ℝ) ^ 3 * B * (T / 2)))
    have hvstar : 0 < vstar := mul_pos hv₀ (Real.exp_pos _)
    obtain ⟨ι, hι, hinj⟩ :=
      exists_uniform_hasInjRadiusAt_pointedMetricSeq (I := I) (M := M) (d := dstar) hB hvstar
    refine ⟨{ ρ := ι, pos := hι, bound := ?_ }⟩
    exact hinj p (fun n => (F n).S.base.metric (T / 2))
      (fun n x => hcurv n (T / 2) hhalf x)
      (fun n x y => riemannianEDistOf_le_of_flowTo (F n) (hτ n) hB
        (fun t ht z => hcurv n t ht z) (hdiam n) hhalf x y)
      (fun n => ofReal_le_volume_univ_of_flowTo (F n) (hτ n) hB
        (fun t ht z => hcurv n t ht z) (hvol n) hhalf)

/-- **D4 with the part-A interface.** The same conclusion when the initial metrics are uniformly
bilipschitz to one fixed smooth reference metric `gRef` (the diameter and volume bounds are then
derived, `exists_uniform_diam_volume_of_bilipschitz`). -/
theorem positiveTimeSlice_canonical_compactness_hypotheses_of_bilipschitz [ConnectedSpace M]
    (gSeq : ℕ → SmoothRiemannianMetric I M)
    (T B : ℝ) (hT : 0 < T) (hB : 0 < B)
    (τ : ℕ → ℝ) (hτ : ∀ n, T < τ n)
    (F : (n : ℕ) → FlowTo (I := I) (M := M) (gSeq n) (τ n))
    (hcurv : ∀ n t, t ∈ Icc 0 T → ∀ x : M,
      Real.sqrt (DifferentialGeometry.Tensor0SBundle.normSq0S
        ((F n).S.base.metric t) x 4
        (metricRm04 ((F n).S.base.metric t) x)) ≤ B)
    (gRef : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 0 < Λ)
    (hbil : ∀ n (x : M) (w : TangentSpace I x),
      (gSeq n).inner x w w ≤ Λ * gRef.inner x w w ∧ gRef.inner x w w ≤ Λ * (gSeq n).inner x w w)
    (p : M) :
    SeqMetricComplete (I := I) (pointedMetricSeq p fun n => (F n).S.base.metric (T / 2)) ∧
      (∀ i : ℕ,
        let _ : TopologicalSpace
            ((pointedMetricSeq p fun n => (F n).S.base.metric (T / 2)).obj i).M :=
          ((pointedMetricSeq p fun n => (F n).S.base.metric (T / 2)).obj i).topology
        ConnectedSpace ((pointedMetricSeq p fun n => (F n).S.base.metric (T / 2)).obj i).M) ∧
      Nonempty (SeqBoundedGeometry (I := I)
        (pointedMetricSeq p fun n => (F n).S.base.metric (T / 2))) ∧
      Nonempty (BaseInjBound (I := I)
        (pointedMetricSeq p fun n => (F n).S.base.metric (T / 2))) := by
  obtain ⟨d, v, hv, huni⟩ := exists_uniform_diam_volume_of_bilipschitz (I := I) gRef hΛ
  exact positiveTimeSlice_canonical_compactness_hypotheses gSeq T B hT hB τ hτ F hcurv hv
    (fun n => (huni (gSeq n) (hbil n)).1) (fun n => (huni (gSeq n) (hbil n)).2) p

/-- **Consumer of D4.** The canonical bounded-geometry compactness supplier applies to the
time-`T/2` slices: a canonical metric compact limit with reference metric equal to the limit metric
and a connected limit. -/
theorem exists_canonical_metric_compactness_of_positiveTime_slices [ConnectedSpace M]
    (gSeq : ℕ → SmoothRiemannianMetric I M)
    (T B : ℝ) (hT : 0 < T) (hB : 0 < B)
    (τ : ℕ → ℝ) (hτ : ∀ n, T < τ n)
    (F : (n : ℕ) → FlowTo (I := I) (M := M) (gSeq n) (τ n))
    (hcurv : ∀ n t, t ∈ Icc 0 T → ∀ x : M,
      Real.sqrt (DifferentialGeometry.Tensor0SBundle.normSq0S
        ((F n).S.base.metric t) x 4
        (metricRm04 ((F n).S.base.metric t) x)) ≤ B)
    {d₀ v₀ : ℝ} (hv₀ : 0 < v₀)
    (hdiam : ∀ n x y, riemannianEDistOf (gSeq n) x y ≤ ENNReal.ofReal d₀)
    (hvol : ∀ n, ENNReal.ofReal v₀ ≤ riemannianVolumeMeasure I M (gSeq n) Set.univ)
    (p : M) :
    ∃ P : MetricCompactLimit (I := I)
        (pointedMetricSeq p fun n => (F n).S.base.metric (T / 2)),
      (∀ k : ℕ, P.convergence.metrics.domain k =
        CanonicalMetricCompactness.canonicalSourceData (I := I) P.maps k) ∧
      (∀ k : ℕ,
        let D := P.convergence.metrics.domain k
        let _ : TopologicalSpace (MetricSourceDomain (I := I) P.maps k) := D.topology
        let _ : ChartedSpace H (MetricSourceDomain (I := I) P.maps k) := D.charted
        let _ : IsManifold I ∞ (MetricSourceDomain (I := I) P.maps k) := D.smooth
        D.referenceMetric = D.limitMetric) ∧
      (let _ : TopologicalSpace P.limit.M := P.limit.topology
       ConnectedSpace P.limit.M) := by
  obtain ⟨hcomplete, hconnected, ⟨hgeom⟩, ⟨hinj⟩⟩ :=
    positiveTimeSlice_canonical_compactness_hypotheses gSeq T B hT hB τ hτ F hcurv hv₀
      hdiam hvol p
  exact exists_canonical_metric_compactness_of_boundedGeometry
    (pointedMetricSeq p fun n => (F n).S.base.metric (T / 2)) hcomplete hconnected hgeom hinj

end DifferentialGeometry.PDE.RicciFlow
