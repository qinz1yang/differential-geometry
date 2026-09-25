import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointReducedLengthWeakLaplacian
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientCurvatureBounds
import DifferentialGeometry.Geometry.Curve.Connecting
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TensorNormFinrankNeZero

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set _root_.MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Analysis.Calculus
open scoped ContDiff _root_.Manifold _root_.Topology BigOperators

universe u uE uH uκ

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)
  (hcar : D.carrier = Iic 0) (hreg : D.regular = Iio 0)
  (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
  (hsigma : ∀ i, 0 < tau i + b)
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}

private local instance : TopologicalSpace F.M := F.topology
private local instance : ChartedSpace H F.M := F.charted
private local instance : IsManifold I ∞ F.M := F.smooth
private local instance : SigmaCompactSpace F.M := F.sigmaCompact
private local instance : T2Space F.M := F.t2

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

local notation "U" => poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
local notation "Y" => poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma

theorem eventually_exists_nhds_integral_poleEndpoint_redLength_chart_laplacian_nonneg_of_ancient
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (p0 : F.M) (a : P.M)
    (hb : b < 0) {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    {K : Set P.M} (hK : IsCompact K)
    {μ : Measure E} [Measure.IsAddHaarMeasure μ] :
    ∀ᶠ k in atTop,
      let metric : ℝ → SmoothRiemannianMetric I P.M :=
        fun s => gSeqExt Phi R bf hsrc htgt k (1 - s)
      let ell : ℝ → P.M → ℝ :=
        fun s y => redLength ((U).term (phi k)).S 0 p0 (Phi.map k y) s
      let f : ℝ × E → ℝ := fun p => scalarOnE (I := I) a (ell p.1) p.2
      let B : ℝ × E → ℝ := fun p => chartDensityOnE (metric p.1) a p.2 *
        ((1 / 2 : ℝ) * normGradSqFun (metric p.1) (ell p.1) ((extChartAt I a).symm p.2) -
          (1 / 2 : ℝ) * ((U).term (phi k)).S.scalar (-p.1)
            (Phi.map k ((extChartAt I a).symm p.2)) +
          ((Module.finrank ℝ E : ℝ) - f p) / (2 * p.1))
      ∀ (J : Set ℝ) (V : Set E), IsOpen J → IsOpen V →
      J ⊆ Ioi 1 → V ⊆ (extChartAt I a).target →
      MapsTo (extChartAt I a).symm V K →
      LocallyLipschitzOn (J ×ˢ V) (f) →
      ∀ A : E →L[ℝ] E →L[ℝ] ℝ,
      (∀ s ∈ J, ConcaveOn ℝ V (fun z => f (s, z) - A z z / 2)) →
      LocallyIntegrableOn (B) (J ×ˢ V) (volume.prod μ) →
      ∀ q0 : ℝ × E, q0 ∈ J ×ˢ V →
      ∃ (J' : Set ℝ) (r : ℝ), IsOpen J' ∧ q0.1 ∈ J' ∧ J' ⊆ J ∧
        0 < r ∧ Metric.ball q0.2 r ⊆ V ∧
        ∀ φ : ℝ × E → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
        tsupport φ ⊆ J' ×ˢ Metric.ball q0.2 r → (∀ p, 0 ≤ φ p) →
        0 ≤ ∫ p, B p * φ p +
          ∑ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            (chartDensityOnE (metric p.1) a p.2 *
              chartInvGramOnE (metric p.1) a ij.1 ij.2 p.2) *
              fderiv ℝ (fun z => f (p.1, z)) p.2 (chartModelBasis E ij.1) *
              fderiv ℝ φ p (0, chartModelBasis E ij.2) ∂volume.prod μ := by
  let _ : NeZero (Module.finrank ℝ E) := by
    obtain ⟨t, _, x, hx⟩ := hF.notFlat
    exact ⟨finrank_ne_zero_of_normSq0S_ne_zero
      (F.S.base.metric t) x (by decide : 0 < 4) (F.S.base.rm04 t x) hx⟩
  let _ : ConnectedSpace F.M := hF.connected
  have hg : RiemannianMetricComplete (F.S.base.metric b) := ⟨hF.complete b hbmem⟩
  obtain ⟨L, hL⟩ := hF.exists_rmNormSq_le
  filter_upwards [eventually_exists_nhds_integral_poleEndpoint_redLength_chart_laplacian_nonneg
    F hcar hreg b hbmem tau q hsigma Phi R bf hsrc htgt p0 a hb hg hK (μ := μ)] with k hk
  intro metric ell f B J V hJ hV hJpos hVt hVK hlip A hconc hB q0 hq0
  apply hk J V hJ hV hJpos hVt hVK ?_ ?_ hlip A hconc hB q0 hq0
  · intro s hs
    refine ⟨L, ?_⟩
    intro t ht y
    apply hL t
    rw [hcar]
    exact ht.2.trans hb.le
  · intro s hs z hz
    exact DifferentialGeometry.exists_contMDiff_curve_endpoints
      (F.S.base.metric b) p0 (Phi.map k ((extChartAt I a).symm z))
      (ne_of_lt (Real.sqrt_pos.mpr (lt_trans zero_lt_one (hJpos hs))))

end DifferentialGeometry.CheegerGromovCompactness
