import DifferentialGeometry.Geometry.Metric.Approximation.FiniteMetric.Curvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.AlmostNonnegativeSectionalApplications
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.PositiveTimeSlice
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.PositiveTimeNoncollapsing
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.SectionalLimitReturn
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.Carrier

/-!
# LFR50: a `C²` metric with nonnegative sectional curvature yields a smooth one

`exists_smooth_sectional_nonneg_of_finite_metric` (the frozen endpoint of design §1 of
`docs/geometrization/chapter13/design-lfr50-merged-20261004.md`): on a compact connected
boundaryless `3`-manifold, a `C^n` Riemannian metric (`n ≥ 2`) whose finite-order sectional
curvature `Bundle.ContMDiffRiemannianMetric.sectionalCurvature` is nonnegative yields a SMOOTH
metric with `sec ≥ 0` on the same manifold.

Proof: part A (`exists_smooth_approximants_of_sectional_nonneg`: smooth approximants with one
`|Rm|` bound, `sec ≥ -εₖ → 0` and one bilipschitz reference) ∘ parts B+C (common Ricci flows with
the error estimate) ∘ part D (positive-time slices satisfy the canonical compactness hypotheses)
∘ parts E+F (limit on the same manifold, recovery of `sec ≥ 0`). No finite-regularity pullback is
used (dispositions, LFR50 item 7).

Variants: `exists_smooth_sectional_nonneg_of_metric2` (`n = 2`, the design's `Metric2`) and
`exists_smooth_sectional_nonneg_of_chart_numerator_nonneg` (the numerator hypothesis of the
design, in chart form). Consumers: the smooth case and a smooth metric regarded as `C²`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.MetricSmoothing

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [CompactSpace M] [BoundarylessManifold I M]

/-- **LFR50 (frozen endpoint).** On a compact connected boundaryless `3`-manifold, a `C^n`
Riemannian metric, `2 ≤ n`, with nonnegative finite-order sectional curvature yields a smooth
Riemannian metric with nonnegative sectional curvature on the same manifold. -/
theorem exists_smooth_sectional_nonneg_of_finite_metric [ConnectedSpace M]
    (hdim : Module.finrank ℝ E = 3) {n : ℕ∞ω} (hn : (2 : ℕ∞ω) ≤ n)
    (g : Bundle.ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (hsec : ∀ x (v w : TangentSpace I x), 0 ≤ g.sectionalCurvature x v w) :
    ∃ h : SmoothRiemannianMetric I M, SectionalBoundedBelow h 0 := by
  obtain ⟨gSeq, B, ε, gRef, Λ, hRm, hε, hεlim, hsecε, hΛ, hbil, -⟩ :=
    exists_smooth_approximants_of_sectional_nonneg g hn hsec
  obtain ⟨d₀, v₀, hv₀, huni⟩ := exists_uniform_diam_volume_of_bilipschitz (I := I) gRef hΛ
  have hdiam : ∀ k (x y : M), riemannianEDistOf (gSeq k) x y ≤ ENNReal.ofReal d₀ :=
    fun k => (huni (gSeq k) (hbil k)).1
  have p : M := Classical.arbitrary M
  obtain ⟨T, hT, hflow⟩ :=
    exists_common_flows_sectional_exp_lower_bound (I := I) hdim B gSeq ε hε hRm hsecε
  choose τ hτ F hF using hflow
  set Bs : ℝ := Real.sqrt (2 * B ^ 2 + 1) with hBs
  have hBpos : 0 < Bs := Real.sqrt_pos.mpr (by positivity)
  have hcurv : ∀ k t, t ∈ Icc 0 T → ∀ x : M,
      Real.sqrt (Tensor0SBundle.normSq0S ((F k).S.base.metric t) x 4
        (metricRm04 ((F k).S.base.metric t) x)) ≤ Bs := fun k t ht => (hF k t ht).1
  have hhalf : T / 2 ∈ Icc 0 T := ⟨by linarith, by linarith⟩
  obtain ⟨hcomplete, -, ⟨hgeom⟩, ⟨hinj⟩⟩ :=
    positiveTimeSlice_canonical_compactness_hypotheses_of_bilipschitz (I := I) gSeq T Bs hT hBpos
      τ hτ F hcurv gRef hΛ hbil p
  refine exists_sectional_nonneg_of_bounded_geometry_limit p
    (fun k => (F k).S.base.metric (T / 2)) hcomplete hgeom hinj
    (Real.exp ((Module.finrank ℝ E : ℝ) ^ 2 * Bs * (T / 2)) * (max d₀ 0 + 1))
    (fun k x y => riemannianEDistOf_le_of_flowTo (F k) (hτ k) hBpos (hcurv k) (hdiam k) hhalf
      x y)
    (fun k => ε k * Real.exp (6 * Bs * (T / 2))) ?_ (fun k => ?_)
  · simpa using hεlim.mul_const (Real.exp (6 * Bs * (T / 2)))
  · simpa [neg_mul] using (hF k (T / 2) hhalf).2

/-- The endpoint for the design's `Metric2 = ContMDiffRiemannianMetric I 2`. -/
theorem exists_smooth_sectional_nonneg_of_metric2 [ConnectedSpace M]
    (hdim : Module.finrank ℝ E = 3)
    (g : Bundle.ContMDiffRiemannianMetric I (2 : ℕ∞ω) E (TangentSpace I : M → Type _))
    (hsec : ∀ x (v w : TangentSpace I x), 0 ≤ g.sectionalCurvature x v w) :
    ∃ h : SmoothRiemannianMetric I M, SectionalBoundedBelow h 0 :=
  exists_smooth_sectional_nonneg_of_finite_metric hdim le_rfl g hsec

/-- The endpoint with the numerator hypothesis of design §1, in chart form: every chart
numerator `Rm(V, W, W, V)` of the finite metric is nonnegative. -/
theorem exists_smooth_sectional_nonneg_of_chart_numerator_nonneg [ConnectedSpace M]
    (hdim : Module.finrank ℝ E = 3) {n : ℕ∞ω} (hn : (2 : ℕ∞ω) ≤ n)
    (g : Bundle.ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (hnum : ∀ q x : M, x ∈ (extChartAt I q).source → ∀ V W : E,
      0 ≤ DifferentialGeometry.Analysis.coefficientRm04 (chartCoeff g q) (extChartAt I q x)
        V W W V) :
    ∃ h : SmoothRiemannianMetric I M, SectionalBoundedBelow h 0 :=
  exists_smooth_sectional_nonneg_of_finite_metric hdim hn g
    ((sectionalCurvature_nonneg_iff_chart_numerator_nonneg (g := g) hn).2 hnum)

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [SigmaCompactSpace M] [CompactSpace M]
  [BoundarylessManifold I M] in
/-- **Regression (smooth case).** For a smooth metric, the finite-order sectional curvature is
the smooth one, so `sec ≥ 0` in the smooth sense gives the finite hypothesis of LFR50. -/
theorem sectionalCurvature_nonneg_of_sectionalBoundedBelow_zero
    (g : SmoothRiemannianMetric I M) (hg : SectionalBoundedBelow g 0) (x : M)
    (v w : TangentSpace I x) : 0 ≤ g.sectionalCurvature x v w := by
  rw [Bundle.ContMDiffRiemannianMetric.sectionalCurvature_eq_smooth,
    DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_def,
    DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureNumerator_eq_metricRm04StandardAt,
    DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator_def]
  have hnum := hg x v w
  rw [zero_mul] at hnum
  refine div_nonneg hnum ?_
  exact DifferentialGeometry.Analysis.bilin_gram_nonneg (B := (g.inner x : E →L[ℝ] E →L[ℝ] ℝ))
    (fun a b => g.symm x a b) (fun u => by
      by_cases hu : u = 0
      · simp [hu]
      · exact (g.pos x u hu).le) v w

/-- **Consumer (smooth case).** LFR50 applies to a smooth metric with `sec ≥ 0`. -/
theorem exists_smooth_sectional_nonneg_of_smooth [ConnectedSpace M]
    (hdim : Module.finrank ℝ E = 3) (g : SmoothRiemannianMetric I M)
    (hg : SectionalBoundedBelow g 0) :
    ∃ h : SmoothRiemannianMetric I M, SectionalBoundedBelow h 0 :=
  exists_smooth_sectional_nonneg_of_finite_metric hdim (by simp) g
    (sectionalCurvature_nonneg_of_sectionalBoundedBelow_zero g hg)

/-- A smooth metric regarded as a `C²` metric (same inner products, regularity forgotten). -/
def SmoothRiemannianMetric.toMetric2 (g : SmoothRiemannianMetric I M) :
    Bundle.ContMDiffRiemannianMetric I (2 : ℕ∞ω) E (TangentSpace I : M → Type _) where
  inner := g.inner
  symm := g.symm
  pos := g.pos
  isVonNBounded := g.isVonNBounded
  contMDiff := g.contMDiff.of_le (by simp)

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M]
  [T2Space M] [CompactSpace M] [BoundarylessManifold I M] in
/-- The finite-order sectional curvature only sees the inner products: it is unchanged when a
smooth metric is regarded as a `C²` metric. -/
theorem sectionalCurvature_toMetric2 (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    (SmoothRiemannianMetric.toMetric2 g).sectionalCurvature x v w = g.sectionalCurvature x v w :=
  rfl

/-- **Consumer (`C²` path).** LFR50 run on the `C²` metric underlying a smooth metric with
`sec ≥ 0`, through the design's `Metric2` endpoint. -/
theorem exists_smooth_sectional_nonneg_of_smooth_via_metric2 [ConnectedSpace M]
    (hdim : Module.finrank ℝ E = 3) (g : SmoothRiemannianMetric I M)
    (hg : SectionalBoundedBelow g 0) :
    ∃ h : SmoothRiemannianMetric I M, SectionalBoundedBelow h 0 :=
  exists_smooth_sectional_nonneg_of_metric2 hdim (SmoothRiemannianMetric.toMetric2 g)
    fun x v w => (sectionalCurvature_toMetric2 g x v w).symm ▸
      sectionalCurvature_nonneg_of_sectionalBoundedBelow_zero g hg x v w

end DifferentialGeometry.Geometry.MetricSmoothing

namespace GC.Endpoint

open DifferentialGeometry.Geometry.MetricSmoothing

universe v

/-- **LFR50 on a carrier with a boundaryless model.** For a compact connected carrier whose
model is boundaryless (`kind = closed`), a `C²` metric with nonnegative finite-order sectional
curvature yields a smooth metric with `sec ≥ 0` on the same carrier. -/
theorem CompactCarrier.exists_smooth_sectional_nonneg_of_metric2 (W : CompactCarrier.{v})
    [W.model.Boundaryless] [ConnectedSpace W.Carrier]
    (g : Bundle.ContMDiffRiemannianMetric W.model (2 : ℕ∞ω) (EuclideanSpace ℝ (Fin 3))
      (TangentSpace W.model : W.Carrier → Type _))
    (hsec : ∀ x (v w : TangentSpace W.model x), 0 ≤ g.sectionalCurvature x v w) :
    ∃ h : SmoothRiemannianMetric W.model W.Carrier, SectionalBoundedBelow h 0 :=
  DifferentialGeometry.Geometry.MetricSmoothing.exists_smooth_sectional_nonneg_of_metric2
    finrank_euclideanSpace_fin g hsec

/-- The closed carrier kind has a boundaryless model, so LFR50 applies directly. -/
theorem CompactCarrier.exists_smooth_sectional_nonneg_of_metric2_of_kind_closed
    (W : CompactCarrier.{v}) (hkind : W.kind = .closed) [ConnectedSpace W.Carrier]
    (g : Bundle.ContMDiffRiemannianMetric W.model (2 : ℕ∞ω) (EuclideanSpace ℝ (Fin 3))
      (TangentSpace W.model : W.Carrier → Type _))
    (hsec : ∀ x (v w : TangentSpace W.model x), 0 ≤ g.sectionalCurvature x v w) :
    ∃ h : SmoothRiemannianMetric W.model W.Carrier, SectionalBoundedBelow h 0 := by
  have : W.model.Boundaryless := by
    unfold CompactCarrier.model
    rw [hkind]
    infer_instance
  exact W.exists_smooth_sectional_nonneg_of_metric2 g hsec

end GC.Endpoint
