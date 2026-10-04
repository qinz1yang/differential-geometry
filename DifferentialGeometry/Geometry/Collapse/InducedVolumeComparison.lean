import DifferentialGeometry.Geometry.Metric.Distance.InducedMetricSpace
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import DifferentialGeometry.Geometry.Comparison.Volume.BishopGromovSectionalThree
import DifferentialGeometry.Geometry.Comparison.Volume.FirstCrossingScale
import DifferentialGeometry.Geometry.Collapse.CurvatureScaleBalls
import DifferentialGeometry.Geometry.Metric.Approximation.RiemannianHausdorffVolume

/-!
# Volume comparison for an arbitrary metric through the induced-metric package

The accepted Bishop–Gromov and volume-scale kernels are bound to an arbitrary smooth Riemannian
metric `g`; no metric-space structure appears in the hypotheses. Every instance that a kernel
needs is installed inside the proof from `g` alone, by the induced-metric package of
`Geometry/Metric/Distance/InducedMetricSpace.lean`.

* T1 (completeness adapter). `RiemannianMetricComplete g` is exactly completeness of the
  extended metric (`riemannianMetricComplete_iff_inducedEMetricSpace`) or of the metric
  (`riemannianMetricComplete_iff_inducedMetricSpace`) induced by `g`; for a given metric space
  whose distance is the one induced by `g`, it is exactly `CompleteSpace`
  (`riemannianMetricComplete_iff_completeSpace`). Consequences: compact closed balls
  (`isCompact_riemannianClosedBallOf`), a proper induced metric
  (`inducedMetricSpace_properSpace_of_riemannianMetricComplete`) and finite volume of every
  ball (`ballVolume_lt_top_of_riemannianMetricComplete`). Finiteness comes from completeness,
  never from a curvature hypothesis.
* T2 (three-dimensional local Bishop–Gromov for an arbitrary complete `g`). Cross, endpoint,
  absolute and relative-ratio comparisons under `sec ≥ -κ` on the ball, and the modified-scale
  bounds LC03 (`C_H = 3 ∫₀¹ sinh²`) and LC04 (`w / (24 ∫₀¹ sinh²)`), for the collapse
  `ballVolume`. The `…_of_le_curvatureRadius` forms take the curvature hypothesis from the
  curvature scale `R_p = curvatureRadius g p` (including the attained radius `R_p` itself).
* T3 (LC01 in the induced metric-measure space). The normalized three-dimensional Hausdorff
  measure of the metric balls of the metric induced by `g` is the collapse `ballVolume`, so the
  first volume scale `r_p(w)` is the first cubic crossing of `r ↦ ℋ³(B(p, r))` and its
  specification holds for `ℋ³`.

Hypotheses of `BishopGromovSectionalThree.lean` discharged by every T2 wrapper: the
`PseudoEMetricSpace` (installed: `inducedEMetricSpace g`), the `RiemannianBundle`
(`⟨g.toRiemannianMetric⟩`), `IsRiemannianManifold` and `IsContinuousRiemannianBundle` (A2),
`CompleteSpace` (T1, from `RiemannianMetricComplete g`), `IsMetricNorm g` (A2),
`NeZero (finrank ℝ E)` (from `finrank ℝ E = 3`) and `T2Space (TangentBundle I M)` (inferred).
The `…_of_le_curvatureRadius` wrappers discharge in addition the sectional hypothesis `hsec`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-! ### T1: the completeness adapter -/

section Adapter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

/-- `RiemannianMetricComplete g` is completeness of the extended metric induced by `g`. -/
theorem riemannianMetricComplete_iff_inducedEMetricSpace
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T3Space M] [SigmaCompactSpace M] {g : SmoothRiemannianMetric I M} :
    RiemannianMetricComplete (I := I) g ↔
      letI := inducedEMetricSpace g
      CompleteSpace M :=
  ⟨fun h => h.complete, fun h => ⟨h⟩⟩

/-- On a connected manifold, `RiemannianMetricComplete g` is completeness of the metric induced
by `g`. -/
theorem riemannianMetricComplete_iff_inducedMetricSpace
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T3Space M] [SigmaCompactSpace M] [ConnectedSpace M] {g : SmoothRiemannianMetric I M} :
    RiemannianMetricComplete (I := I) g ↔
      letI := inducedMetricSpace g
      CompleteSpace M :=
  ⟨fun h => h.complete, fun h => ⟨h⟩⟩

/-- For a given extended metric space whose extended distance is the `g`-length distance,
`RiemannianMetricComplete g` is its completeness. -/
theorem riemannianMetricComplete_iff_completeSpace_of_edist
    {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M}
    (hedist : ∀ a b : M, edist a b = riemannianEDistOf (I := I) g a b) :
    RiemannianMetricComplete (I := I) g ↔ CompleteSpace M := by
  have heq : (inducedEMetricSpace g).toPseudoEMetricSpace =
      (‹EMetricSpace M›).toPseudoEMetricSpace := by
    apply PseudoEMetricSpace.ext
    ext a b
    exact (hedist a b).symm
  rw [riemannianMetricComplete_iff_inducedEMetricSpace]
  exact (congrArg (@CompleteSpace M)
    (congrArg (fun m : PseudoEMetricSpace M => m.toUniformSpace) heq)).to_iff

/-- The adapter for a given metric space (the design's context A): if the distance is the one
induced by `g` (`hmetric`), then `RiemannianMetricComplete g` is exactly `CompleteSpace M`. -/
theorem riemannianMetricComplete_iff_completeSpace
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M}
    (hmetric : ∀ a b : M, riemannianEDistOf (I := I) g a b = ENNReal.ofReal (dist a b)) :
    RiemannianMetricComplete (I := I) g ↔ CompleteSpace M :=
  riemannianMetricComplete_iff_completeSpace_of_edist fun a b => by
    rw [hmetric, edist_dist]

end Adapter

/-! ### T1: compact closed balls and finite ball volumes from completeness -/

section Consequences

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

/-- Closed `g`-balls of a complete metric are compact (Hopf–Rinow). -/
theorem isCompact_riemannianClosedBallOf {g : SmoothRiemannianMetric I M}
    (hg : RiemannianMetricComplete (I := I) g) (p : M) (r : ℝ) :
    IsCompact (riemannianClosedBallOf g p r) :=
  hg.closedEBall_isCompact p r

/-- The metric induced by a complete `g` is proper. -/
theorem inducedMetricSpace_properSpace_of_riemannianMetricComplete [T3Space M] [ConnectedSpace M]
    {g : SmoothRiemannianMetric I M} (hg : RiemannianMetricComplete (I := I) g) :
    letI := inducedMetricSpace g
    ProperSpace M := by
  let := inducedMetricSpace g
  refine ProperSpace.of_isCompact_closedBall_of_le 0 fun p r hr => ?_
  rw [inducedMetricSpace_closedBall g p hr]
  exact isCompact_riemannianClosedBallOf hg p r

/-- Every closed `g`-ball of a complete metric has finite Riemannian volume. -/
theorem riemannianVolumeMeasure_riemannianClosedBallOf_lt_top {g : SmoothRiemannianMetric I M}
    (hg : RiemannianMetricComplete (I := I) g) (p : M) (r : ℝ) :
    Integral.Measure.riemannianVolumeMeasure I M g (riemannianClosedBallOf g p r) < ⊤ := by
  let : MeasurableSpace M := borel M
  have : BorelSpace M := ⟨rfl⟩
  have := Integral.Measure.riemannianVolumeMeasure_isLocallyFiniteMeasure (I := I) g
  exact (isCompact_riemannianClosedBallOf hg p r).measure_lt_top

/-- Every `g`-ball of a complete metric has finite Riemannian volume. No curvature hypothesis
is involved. -/
theorem ballVolume_lt_top_of_riemannianMetricComplete {g : SmoothRiemannianMetric I M}
    (hg : RiemannianMetricComplete (I := I) g) (p : M) (r : ℝ) :
    Geometry.Collapse.ballVolume g p r < ⊤ := by
  let : MeasurableSpace M := borel M
  have hsub : riemannianBallOf g p r ⊆ riemannianClosedBallOf g p r := fun q hq => by
    change riemannianEDistOf (I := I) g p q < ENNReal.ofReal r at hq
    exact hq.le
  exact (measure_mono hsub).trans_lt
    (riemannianVolumeMeasure_riemannianClosedBallOf_lt_top hg p r)

/-- Context A: for a given complete metric space whose distance is the one induced by `g`,
every `g`-ball has finite Riemannian volume. -/
theorem ballVolume_lt_top_of_completeSpace
    {M' : Type*} [MetricSpace M'] [CompleteSpace M'] [ChartedSpace H M'] [IsManifold I ∞ M']
    [SigmaCompactSpace M'] (g : SmoothRiemannianMetric I M')
    (hmetric : ∀ a b : M', riemannianEDistOf (I := I) g a b = ENNReal.ofReal (dist a b))
    (p : M') (r : ℝ) :
    Geometry.Collapse.ballVolume g p r < ⊤ :=
  ballVolume_lt_top_of_riemannianMetricComplete
    ((riemannianMetricComplete_iff_completeSpace hmetric).mpr ‹_›) p r

end Consequences

/-! ### T2: three-dimensional local Bishop–Gromov for an arbitrary complete metric -/

namespace Geometry.Collapse

open Geometry.Riemannian
open Geometry.Riemannian.VolumeComparison (modelVolume collapseBallVolume_eq_comparison
  localBishopGromov_cross_sectional_three localBishopGromov_cross_endpoint_sectional_three
  localBishopGromov_upper_sectional_three localBishopGromov_relative_ratios_sectional_three
  sectionalThree_volume_upper_at_modified_scale sectionalThree_volume_lower_at_modified_scale
  sectionalThree_scaled_volume_upper_at_modified_scale)

section CurvatureScale

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- The defining sectional bound of the curvature scale on every ball of radius `r ≤ R_p`,
including the attained radius `r = R_p` (A1 T1, strict and attained). -/
theorem sectionalBoundedBelowAt_of_ofReal_le_curvatureRadius (g : SmoothRiemannianMetric I M)
    {p : M} {r : ℝ} (hr : 0 < r) (hR : ENNReal.ofReal r ≤ curvatureRadius g p) :
    ∀ q ∈ riemannianBallOf g p r, SectionalBoundedBelowAt g q (-(r ^ 2)⁻¹) := by
  rcases hR.lt_or_eq with hlt | heq
  · exact fun q hq => sectionalBoundedBelowAt_of_lt_curvatureRadius g hlt hq
  · have hfin : curvatureRadius g p ≠ ⊤ := heq ▸ ENNReal.ofReal_ne_top
    have hreal : (curvatureRadius g p).toReal = r := by
      rw [← heq, ENNReal.toReal_ofReal hr.le]
    simpa only [hreal] using sectionalBoundedBelowAt_of_curvatureRadius_ne_top g hfin

end CurvatureScale

section Comparison

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

omit [I.Boundaryless] [ConnectedSpace M] in
/-- The induced-metric package as an eliminator: every instance of the three-dimensional
comparison kernels of `BishopGromovSectionalThree.lean` is installed from `g` alone (A2), with
completeness from `RiemannianMetricComplete g` (T1). -/
private theorem inducedPackage_elim (g : SmoothRiemannianMetric I M)
    (hg : RiemannianMetricComplete (I := I) g) (hdim : Module.finrank ℝ E = 3) {P : Prop}
    (h : ∀ [NeZero (Module.finrank ℝ E)] [PseudoEMetricSpace M]
      [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
      [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] [CompleteSpace M],
      IsMetricNorm (I := I) g → P) : P := by
  have : T3Space M := by
    let := Manifold.metrizableSpace I M
    infer_instance
  have : NeZero (Module.finrank ℝ E) := ⟨by rw [hdim]; norm_num⟩
  let := inducedEMetricSpace g
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have : IsRiemannianManifold I M := inducedEMetricSpace_isRiemannianManifold g
  have : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    isContinuousRiemannianBundle_of_smoothRiemannianMetric g
  have : CompleteSpace M := riemannianMetricComplete_iff_inducedEMetricSpace.mp hg
  exact h (isMetricNorm_of_smoothRiemannianMetric g)

/-- Local Bishop–Gromov with a radial margin `R < R₀`, for an arbitrary complete metric. -/
theorem ballVolume_cross_of_sectional_three (g : SmoothRiemannianMetric I M)
    (hg : RiemannianMetricComplete (I := I) g) (hdim : Module.finrank ℝ E = 3) (p : M)
    {κ s R R₀ : ℝ} (hκ : 0 ≤ κ) (hs : 0 < s) (hsR : s ≤ R) (hRR₀ : R < R₀)
    (hsec : ∀ q ∈ riemannianBallOf g p R₀, SectionalBoundedBelowAt g q (-κ)) :
    ballVolume g p R * ENNReal.ofReal (modelVolume (-κ) 3 s) ≤
      ENNReal.ofReal (modelVolume (-κ) 3 R) * ballVolume g p s := by
  refine inducedPackage_elim g hg hdim fun hEnorm => ?_
  rw [collapseBallVolume_eq_comparison g hEnorm, collapseBallVolume_eq_comparison g hEnorm]
  exact localBishopGromov_cross_sectional_three g hEnorm hdim p hκ hs hsR hRR₀ hsec

/-- Local Bishop–Gromov at the endpoint: the sectional bound only on the ball of radius `R`. -/
theorem ballVolume_cross_endpoint_of_sectional_three (g : SmoothRiemannianMetric I M)
    (hg : RiemannianMetricComplete (I := I) g) (hdim : Module.finrank ℝ E = 3) (p : M)
    {κ s R : ℝ} (hκ : 0 ≤ κ) (hs : 0 < s) (hsR : s ≤ R)
    (hsec : ∀ q ∈ riemannianBallOf g p R, SectionalBoundedBelowAt g q (-κ)) :
    ballVolume g p R * ENNReal.ofReal (modelVolume (-κ) 3 s) ≤
      ENNReal.ofReal (modelVolume (-κ) 3 R) * ballVolume g p s := by
  refine inducedPackage_elim g hg hdim fun hEnorm => ?_
  rw [collapseBallVolume_eq_comparison g hEnorm, collapseBallVolume_eq_comparison g hEnorm]
  exact localBishopGromov_cross_endpoint_sectional_three g hEnorm hdim p hκ hs hsR hsec

/-- The absolute local Bishop–Gromov upper bound by the model volume. -/
theorem ballVolume_le_modelVolume_of_sectional_three (g : SmoothRiemannianMetric I M)
    (hg : RiemannianMetricComplete (I := I) g) (hdim : Module.finrank ℝ E = 3) (p : M)
    {κ R : ℝ} (hκ : 0 ≤ κ) (hR : 0 < R)
    (hsec : ∀ q ∈ riemannianBallOf g p R, SectionalBoundedBelowAt g q (-κ)) :
    ballVolume g p R ≤ ENNReal.ofReal (modelVolume (-κ) 3 R) := by
  refine inducedPackage_elim g hg hdim fun hEnorm => ?_
  rw [collapseBallVolume_eq_comparison g hEnorm]
  exact localBishopGromov_upper_sectional_three g hEnorm hdim p hκ hR hsec

/-- The relative volume ratios of concentric balls, with positivity and finiteness. -/
theorem ballVolume_relative_ratios_of_sectional_three (g : SmoothRiemannianMetric I M)
    (hg : RiemannianMetricComplete (I := I) g) (hdim : Module.finrank ℝ E = 3) (p : M)
    {κ s R : ℝ} (hκ : 0 ≤ κ) (hs : 0 < s) (hsR : s ≤ R)
    (hsec : ∀ q ∈ riemannianBallOf g p R, SectionalBoundedBelowAt g q (-κ)) :
    0 < (ballVolume g p s).toReal ∧ 0 < (ballVolume g p R).toReal ∧
      ballVolume g p s < ⊤ ∧ ballVolume g p R < ⊤ ∧
      (ballVolume g p R).toReal / (ballVolume g p s).toReal ≤
        modelVolume (-κ) 3 R / modelVolume (-κ) 3 s ∧
      modelVolume (-κ) 3 s / modelVolume (-κ) 3 R ≤
        (ballVolume g p s).toReal / (ballVolume g p R).toReal := by
  refine inducedPackage_elim g hg hdim fun hEnorm => ?_
  rw [collapseBallVolume_eq_comparison g hEnorm, collapseBallVolume_eq_comparison g hEnorm]
  exact localBishopGromov_relative_ratios_sectional_three g hEnorm hdim p hκ hs hsR hsec

/-- LC03: the volume upper bound at twice the modified scale, `C_H = 3 ∫₀¹ sinh²`. -/
theorem ballVolume_twice_scale_le_of_attained (g : SmoothRiemannianMetric I M)
    (hg : RiemannianMetricComplete (I := I) g) (hdim : Module.finrank ℝ E = 3) (p : M)
    {w r ρ : ℝ} (hw : 0 < w) (hr : 0 < r) (hρ : 0 < ρ) (hrρ : r ≤ 2 * ρ)
    (hvol : ballVolume g p r = ENNReal.ofReal (w * r ^ 3))
    (hsec : ∀ q ∈ riemannianBallOf g p (2 * ρ),
      SectionalBoundedBelowAt g q (-((2 * ρ) ^ 2)⁻¹)) :
    (ballVolume g p (2 * ρ)).toReal / (2 * ρ) ^ 3 ≤
      (3 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) * w :=
  inducedPackage_elim g hg hdim fun hEnorm =>
    sectionalThree_volume_upper_at_modified_scale g hEnorm hdim p hw hr hρ hrρ hvol hsec

/-- LC03 after rescaling by `ρ⁻²`: the radius-`2` ball has volume at most `8 C_H w`. -/
theorem ballVolume_rescaled_two_le_of_attained (g : SmoothRiemannianMetric I M)
    (hg : RiemannianMetricComplete (I := I) g) (hdim : Module.finrank ℝ E = 3) (p : M)
    {w r ρ : ℝ} (hw : 0 < w) (hr : 0 < r) (hρ : 0 < ρ) (hrρ : r ≤ 2 * ρ)
    (hvol : ballVolume g p r = ENNReal.ofReal (w * r ^ 3))
    (hsec : ∀ q ∈ riemannianBallOf g p (2 * ρ),
      SectionalBoundedBelowAt g q (-((2 * ρ) ^ 2)⁻¹)) :
    (ballVolume (scaleMetric (ρ ^ 2)⁻¹ (inv_pos.mpr (sq_pos_of_pos hρ)) g) p 2).toReal ≤
      8 * (3 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) * w :=
  inducedPackage_elim g hg hdim fun hEnorm =>
    sectionalThree_scaled_volume_upper_at_modified_scale g hEnorm hdim p hw hr hρ hrρ hvol hsec

/-- LC04: the lower volume bound `w / (24 ∫₀¹ sinh²)` for a radius `ρ ≤ 2u`. The finiteness of
the ball of radius `ρ` comes from completeness, not from the curvature bound on `B(p, u)`. -/
theorem ballVolume_scale_lower_of_attained (g : SmoothRiemannianMetric I M)
    (hg : RiemannianMetricComplete (I := I) g) (hdim : Module.finrank ℝ E = 3) (p : M)
    {w u ρ : ℝ} (hw : 0 < w) (hu : 0 < u) (hρ : 0 < ρ) (hρu : ρ ≤ 2 * u)
    (hvol : ballVolume g p u = ENNReal.ofReal (w * u ^ 3))
    (hsec : ∀ q ∈ riemannianBallOf g p u, SectionalBoundedBelowAt g q (-(u ^ 2)⁻¹)) :
    0 < w / (24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) ∧
      w / (24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) ≤ (ballVolume g p ρ).toReal / ρ ^ 3 :=
  inducedPackage_elim g hg hdim fun hEnorm =>
    sectionalThree_volume_lower_at_modified_scale g hEnorm hdim p hw hu hρ hρu hvol hsec

/-- Absolute local Bishop–Gromov at the curvature scale: for `0 < R` with `R ≤ R_p`,
`Vol B(p, R) / R³ ≤ 4π ∫₀¹ sinh²`. -/
theorem ballVolume_div_cube_le_of_le_curvatureRadius (g : SmoothRiemannianMetric I M)
    (hg : RiemannianMetricComplete (I := I) g) (hdim : Module.finrank ℝ E = 3) (p : M)
    {R : ℝ} (hR : 0 < R) (hRp : ENNReal.ofReal R ≤ curvatureRadius g p) :
    (ballVolume g p R).toReal / R ^ 3 ≤ 4 * Real.pi * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2 := by
  have hupper := ballVolume_le_modelVolume_of_sectional_three g hg hdim p
    (inv_nonneg.mpr (sq_nonneg R)) hR
    (sectionalBoundedBelowAt_of_ofReal_le_curvatureRadius g hR hRp)
  rw [VolumeComparison.sectionalThree_model_at_inverse_radius hR,
    VolumeComparison.sectionalThree_model_hyperbolic_integral, euclideanUnitBallVolume_three_eq]
    at hupper
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hupper
  rw [ENNReal.toReal_ofReal (by
    have := VolumeComparison.sectionalThree_hyperbolic_integral_pos
    positivity)] at hreal
  rw [div_le_iff₀ (pow_pos hR 3)]
  linarith only [hreal]

/-- LC03 at the curvature scale: the sectional hypothesis is discharged by
`2ρ ≤ R_p = curvatureRadius g p`. -/
theorem ballVolume_twice_scale_le_of_le_curvatureRadius (g : SmoothRiemannianMetric I M)
    (hg : RiemannianMetricComplete (I := I) g) (hdim : Module.finrank ℝ E = 3) (p : M)
    {w r ρ : ℝ} (hw : 0 < w) (hr : 0 < r) (hρ : 0 < ρ) (hrρ : r ≤ 2 * ρ)
    (hvol : ballVolume g p r = ENNReal.ofReal (w * r ^ 3))
    (hRp : ENNReal.ofReal (2 * ρ) ≤ curvatureRadius g p) :
    (ballVolume g p (2 * ρ)).toReal / (2 * ρ) ^ 3 ≤
      (3 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) * w :=
  ballVolume_twice_scale_le_of_attained g hg hdim p hw hr hρ hrρ hvol
    (sectionalBoundedBelowAt_of_ofReal_le_curvatureRadius g (by positivity) hRp)

/-- LC04 at the curvature scale: the sectional hypothesis is discharged by `u ≤ R_p`. -/
theorem ballVolume_scale_lower_of_le_curvatureRadius (g : SmoothRiemannianMetric I M)
    (hg : RiemannianMetricComplete (I := I) g) (hdim : Module.finrank ℝ E = 3) (p : M)
    {w u ρ : ℝ} (hw : 0 < w) (hu : 0 < u) (hρ : 0 < ρ) (hρu : ρ ≤ 2 * u)
    (hvol : ballVolume g p u = ENNReal.ofReal (w * u ^ 3))
    (hRp : ENNReal.ofReal u ≤ curvatureRadius g p) :
    0 < w / (24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) ∧
      w / (24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) ≤ (ballVolume g p ρ).toReal / ρ ^ 3 :=
  ballVolume_scale_lower_of_attained g hg hdim p hw hu hρ hρu hvol
    (sectionalBoundedBelowAt_of_ofReal_le_curvatureRadius g hu hRp)

end Comparison


/-! ### T3: LC01 in the metric-measure space induced by `g` -/

section Hausdorff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T3Space M] [SigmaCompactSpace M] [ConnectedSpace M]

/-- In the metric space induced by `g` (A2), the normalized three-dimensional Hausdorff measure
of every metric ball is the collapse `ballVolume` (A3's exact identity). -/
theorem normalizedHausdorffMeasure_ball_eq_ballVolume (g : SmoothRiemannianMetric I M)
    (hdim : Module.finrank ℝ E = 3) (p : M) (r : ℝ) :
    letI := inducedMetricSpace g
    letI : MeasurableSpace M := borel M
    haveI : BorelSpace M := ⟨rfl⟩
    normalizedHausdorffMeasure 3 (Metric.ball p r) = ballVolume g p r := by
  let := inducedMetricSpace g
  let : MeasurableSpace M := borel M
  have : BorelSpace M := ⟨rfl⟩
  rw [inducedMetricSpace_ball g p r]
  exact congrArg (fun μ : Measure M => μ (riemannianBallOf g p r))
    (Metric.lengthMetric_normalizedHausdorffMeasure_three_eq_riemannianVolumeMeasure g hdim)

/-- The first volume scale is a metric-measure invariant of the metric induced by `g`: it is the
first cubic crossing of `r ↦ ℋ³(B(p, r))`. -/
theorem firstVolumeScale_eq_firstPositiveCrossing_normalizedHausdorffMeasure
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 3) (p : M) (w : ℝ) :
    letI := inducedMetricSpace g
    letI : MeasurableSpace M := borel M
    haveI : BorelSpace M := ⟨rfl⟩
    firstVolumeScale g p w = Real.firstPositiveCrossing
      (fun r => (normalizedHausdorffMeasure 3 (Metric.ball p r)).toReal) (fun r => w * r ^ 3) := by
  let := inducedMetricSpace g
  let : MeasurableSpace M := borel M
  have : BorelSpace M := ⟨rfl⟩
  simp only [normalizedHausdorffMeasure_ball_eq_ballVolume g hdim p]
  rfl

/-- LC01 for `ℋ³` of the metric induced by `g` on a closed connected three-manifold: positivity,
attainment and the strict earlier inequality, in `ℝ≥0∞`. Strict antitonicity in `w` is
`firstVolumeScale_strictAntiOn` (X67) and involves no measure. -/
theorem firstVolumeScale_spec_normalizedHausdorffMeasure [I.Boundaryless] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 3) (p : M) {w : ℝ}
    (hw : 0 < w) (hwc : w < 4 * Real.pi / 3) :
    letI := inducedMetricSpace g
    letI : MeasurableSpace M := borel M
    haveI : BorelSpace M := ⟨rfl⟩
    0 < firstVolumeScale g p w ∧
      normalizedHausdorffMeasure 3 (Metric.ball p (firstVolumeScale g p w)) =
        ENNReal.ofReal (w * firstVolumeScale g p w ^ 3) ∧
      ∀ r : ℝ, 0 < r → r < firstVolumeScale g p w →
        ENNReal.ofReal (w * r ^ 3) < normalizedHausdorffMeasure 3 (Metric.ball p r) := by
  let := inducedMetricSpace g
  let : MeasurableSpace M := borel M
  have : BorelSpace M := ⟨rfl⟩
  obtain ⟨hpos, -, hbefore⟩ := firstVolumeScale_spec g hdim p hw hwc
  simp only [normalizedHausdorffMeasure_ball_eq_ballVolume g hdim p]
  refine ⟨hpos, ballVolume_firstVolumeScale g hdim p hw hwc, fun r hr hrr => ?_⟩
  rw [ENNReal.ofReal_lt_iff_lt_toReal (mul_pos hw (pow_pos hr 3)).le (ballVolume_ne_top g p r)]
  exact hbefore r hr hrr

end Hausdorff

end Geometry.Collapse

end DifferentialGeometry
