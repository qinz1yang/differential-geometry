import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointChartUpperContact
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.PositiveRankOneCoefficients
import DifferentialGeometry.Analysis.Parabolic.WeakEquation.MatrixDrift
import DifferentialGeometry.Analysis.Calculus.Derivative.LocallyLipschitz
import DifferentialGeometry.Geometry.Coordinates.Fields.ScalarDifferentiability

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set _root_.MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Analysis.Calculus
open scoped ContDiff _root_.Manifold _root_.Topology BigOperators

universe u uE uH uκ

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
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

theorem eventually_ae_exists_poleEndpoint_redLength_chart_upper_contacts
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (p0 : F.M) (a : P.M)
    (hb : b < 0) (hg : RiemannianMetricComplete (F.S.base.metric b))
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
      ∀ {κ : Type uκ} [Fintype κ], ∀ (J : Set ℝ) (V : Set E), IsOpen J → IsOpen V →
      J ⊆ Ioi 0 → V ⊆ (extChartAt I a).target →
      MapsTo (extChartAt I a).symm V K →
      (∀ s ∈ J, ∃ L : ℝ, ∀ t ∈ Icc (b - s / (tau (phi k) + b)⁻¹) b, ∀ y : F.M,
        normSq0S (F.S.base.metric t) y 4 (F.S.base.rm04 t y) ≤ L) →
      (∀ s ∈ J, ∀ z ∈ V, ∃ alpha : ℝ → F.M,
        ContMDiff 𝓘(ℝ, ℝ) I 1 alpha ∧ alpha 0 = p0 ∧
          alpha (Real.sqrt s) = Phi.map k ((extChartAt I a).symm z)) →
      LocallyLipschitzOn (J ×ˢ V) (f) →
      ∀ (v : κ → E) (w : κ → ℝ × E → ℝ),
      (∀ p ∈ J ×ˢ V, ∀ i j : Fin (Module.finrank ℝ E),
        chartDensityOnE (metric p.1) a p.2 *
          chartInvGramOnE (metric p.1) a i j p.2 =
          ∑ m, w m p * (chartModelBasis E).repr (v m) i *
            (chartModelBasis E).repr (v m) j) →
      ∀ᵐ p ∂volume.prod μ, p ∈ J ×ˢ V → ∀ ε : ℝ, 0 < ε →
      ∃ ψ : κ → ℝ → ℝ, (∀ j, ContDiffAt ℝ 2 (ψ j) 0) ∧
        (∀ j, ∀ᶠ t in 𝓝 0, f (p.1, p.2 + t • v j) ≤ ψ j t) ∧
        (∀ j, f p = ψ j 0) ∧
        (∑ j, w j p * deriv (deriv (ψ j)) 0) ≤ B p -
          (∑ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            fderiv ℝ (fun z => chartDensityOnE (metric p.1) a z *
              chartInvGramOnE (metric p.1) a ij.1 ij.2 z) p.2
                (chartModelBasis E ij.1) *
              fderiv ℝ (fun z => f (p.1, z)) p.2 (chartModelBasis E ij.2)) + ε := by
  classical
  filter_upwards [eventually_exists_poleEndpoint_redLength_chart_upper_contacts
    F hcar hreg b hbmem tau q hsigma Phi R bf hsrc htgt hb hg hK] with k hk
  intro metric ell f B κ instκ J V hJ hV hJpos hVt hVK hRm hcurve hlip v w hC
  filter_upwards [hlip.ae_differentiableAt_of_isOpen
    (μ := volume.prod μ) (hJ.prod hV)] with p hp hpJV ε hε
  have hjoint : DifferentiableAt ℝ (f) p := hp hpJV
  have hslice : DifferentiableAt ℝ (fun z : E => (p.1, z)) p.2 :=
    (differentiableAt_const p.1).prodMk differentiableAt_id
  have hdf : DifferentiableAt ℝ (fun z => f (p.1, z)) p.2 := by
    simpa only [Function.comp_def] using
      DifferentiableAt.comp (𝕜 := ℝ) (g := f) (f := fun z : E => (p.1, z))
        p.2 hjoint hslice
  have hmd : MDifferentiableAt I 𝓘(ℝ, ℝ) (ell p.1)
      ((extChartAt I a).symm p.2) :=
    mdifferentiableAt_of_differentiableAt_scalarOnE (hVt hpJV.2) hdf
  obtain ⟨alpha, halpha, ha0, hat⟩ := hcurve p.1 hpJV.1 p.2 hpJV.2
  obtain ⟨L, hL⟩ := hRm p.1 hpJV.1
  have hcoeff : ∀ i j : Fin (Module.finrank ℝ E),
      chartDensityOnE (gSeqExt Phi R bf hsrc htgt k (1 - p.1)) a p.2 *
        chartInvGramOnE (gSeqExt Phi R bf hsrc htgt k (1 - p.1)) a i j p.2 =
        ∑ m, w m p * (chartModelBasis E).repr (v m) i *
          (chartModelBasis E).repr (v m) j := hC p hpJV
  specialize hk (κ := κ) p0 a p.2 (hVt hpJV.2) (hVK hpJV.2)
    p.1 (hJpos hpJV.1) L hL alpha halpha ha0 hat hmd v (fun j => w j p)
  specialize hk hcoeff ε hε
  obtain ⟨ψ, hψ, hupper, heq, hbound⟩ := hk
  refine ⟨ψ, hψ, hupper, heq, ?_⟩
  convert hbound using 1
  simp only [B, f, ell, metric, iteratedFDeriv_one_apply, scalarOnE]
  rfl

theorem eventually_integral_poleEndpoint_redLength_chart_laplacian_nonneg
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (p0 : F.M) (a : P.M)
    (hb : b < 0) (hg : RiemannianMetricComplete (F.S.base.metric b))
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
      ∀ {κ : Type uκ} [Fintype κ], ∀ (J : Set ℝ) (V : Set E), IsOpen J → IsOpen V →
      J ⊆ Ioi 0 → V ⊆ (extChartAt I a).target →
      MapsTo (extChartAt I a).symm V K →
      (∀ s ∈ J, ∃ L : ℝ, ∀ t ∈ Icc (b - s / (tau (phi k) + b)⁻¹) b, ∀ y : F.M,
        normSq0S (F.S.base.metric t) y 4 (F.S.base.rm04 t y) ≤ L) →
      (∀ s ∈ J, ∀ z ∈ V, ∃ alpha : ℝ → F.M,
        ContMDiff 𝓘(ℝ, ℝ) I 1 alpha ∧ alpha 0 = p0 ∧
          alpha (Real.sqrt s) = Phi.map k ((extChartAt I a).symm z)) →
      LocallyLipschitzOn (J ×ˢ V) (f) →
      ∀ A : E →L[ℝ] E →L[ℝ] ℝ,
      (∀ s ∈ J, ConcaveOn ℝ V (fun z => f (s, z) - A z z / 2)) →
      ∀ (v : κ → E) (w : κ → ℝ × E → ℝ),
      (∀ j, ContDiffOn ℝ 2 (w j) (J ×ˢ V)) →
      (∀ j, ∀ p ∈ J ×ˢ V, 0 ≤ w j p) →
      (∀ p ∈ J ×ˢ V, ∀ i j : Fin (Module.finrank ℝ E),
        chartDensityOnE (metric p.1) a p.2 *
          chartInvGramOnE (metric p.1) a i j p.2 =
          ∑ m, w m p * (chartModelBasis E).repr (v m) i *
            (chartModelBasis E).repr (v m) j) →
      LocallyIntegrableOn (B) (J ×ˢ V) (volume.prod μ) →
      ∀ φ : ℝ × E → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      tsupport φ ⊆ J ×ˢ V → (∀ p, 0 ≤ φ p) →
      0 ≤ ∫ p, B p * φ p +
        ∑ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          (chartDensityOnE (metric p.1) a p.2 *
            chartInvGramOnE (metric p.1) a ij.1 ij.2 p.2) *
            fderiv ℝ (fun z => f (p.1, z)) p.2 (chartModelBasis E ij.1) *
            fderiv ℝ φ p (0, chartModelBasis E ij.2) ∂volume.prod μ := by
  classical
  filter_upwards [eventually_ae_exists_poleEndpoint_redLength_chart_upper_contacts
    F hcar hreg b hbmem tau q hsigma Phi R bf hsrc htgt p0 a hb hg hK (μ := μ)] with k hk
  intro metric ell f B κ instκ J V hJ hV hJpos hVt hVK hRm hcurve hlip A hconc v w hw hwn hC hB
    φ hφ hφc hφV hφn
  have hcontact := hk (κ := κ) J V hJ hV hJpos hVt hVK hRm hcurve hlip v w hC
  exact integral_add_matrix_spatial_derivative_mul_nonneg_of_ae_approximate_upper_contacts
    hlip hJ hV A hconc (chartModelBasis E) v w hw hwn
    (fun i j p => chartDensityOnE (metric p.1) a p.2 *
      chartInvGramOnE (metric p.1) a i j p.2)
    hC (B) hB hcontact φ hφ hφc hφV hφn


theorem eventually_exists_nhds_integral_poleEndpoint_redLength_chart_laplacian_nonneg
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (p0 : F.M) (a : P.M)
    (hb : b < 0) (hg : RiemannianMetricComplete (F.S.base.metric b))
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
      (∀ s ∈ J, ∃ L : ℝ, ∀ t ∈ Icc (b - s / (tau (phi k) + b)⁻¹) b, ∀ y : F.M,
        normSq0S (F.S.base.metric t) y 4 (F.S.base.rm04 t y) ≤ L) →
      (∀ s ∈ J, ∀ z ∈ V, ∃ alpha : ℝ → F.M,
        ContMDiff 𝓘(ℝ, ℝ) I 1 alpha ∧ alpha 0 = p0 ∧
          alpha (Real.sqrt s) = Phi.map k ((extChartAt I a).symm z)) →
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
  classical
  obtain ⟨N0, hN0⟩ := bf.grow_cover K hK
  filter_upwards [eventually_integral_poleEndpoint_redLength_chart_laplacian_nonneg
    F hcar hreg b hbmem tau q hsigma Phi R bf hsrc htgt p0 a hb hg hK (μ := μ),
    eventually_ge_atTop N0] with k hk hkN
  intro metric ell f B J V hJ hV hJpos hVt hVK hRm hcurve hlip A hconc hB q0 hq0
  have hqt : 1 - q0.1 ∈ (Y).D.regular := by
    change 1 - q0.1 < 0
    have hpos : 1 < q0.1 := hJpos hq0.1
    linarith
  obtain ⟨N, v, w, O, hO, hqO, _, hw, hwp, hrep⟩ :=
    exists_contDiffOn_gSeqExt_positive_rank_one_decomposition_one_sub
      Phi R bf hsrc htgt k a q0 hqt (hVt hq0.2) (hN0 k hkN (hVK hq0.2)) 2
  obtain ⟨J', V', hJ', hV', hqJ', hqV', hrect⟩ :=
    isOpen_prod_iff.mp (hO.inter (hJ.prod hV)) q0.1 q0.2 ⟨hqO, hq0⟩
  obtain ⟨r, hr, hrV'⟩ := Metric.isOpen_iff.mp hV' q0.2 hqV'
  have hJ'J : J' ⊆ J := fun s hs => (hrect (a := (s, q0.2)) ⟨hs, hqV'⟩).2.1
  have hballV : Metric.ball q0.2 r ⊆ V :=
    fun z hz => (hrect (a := (q0.1, z)) ⟨hqJ', hrV' hz⟩).2.2
  have hsmallO : J' ×ˢ Metric.ball q0.2 r ⊆ O :=
    fun p hp => (hrect (a := p) ⟨hp.1, hrV' hp.2⟩).1
  have hsmallJV : J' ×ˢ Metric.ball q0.2 r ⊆ J ×ˢ V :=
    fun p hp => ⟨hJ'J hp.1, hballV hp.2⟩
  refine ⟨J', r, hJ', hqJ', hJ'J, hr, hballV, ?_⟩
  intro φ hφ hφc hφV hφn
  apply hk (κ := Fin N) J' (Metric.ball q0.2 r) hJ' Metric.isOpen_ball
    (fun s hs => (show (0 : ℝ) < s from lt_trans zero_lt_one (hJpos (hJ'J hs)))) (hballV.trans hVt)
    (fun _ hz => hVK (hballV hz))
    (fun s hs => hRm s (hJ'J hs))
    (fun s hs z hz => hcurve s (hJ'J hs) z (hballV hz))
    (hlip.mono hsmallJV) A
    (fun s hs => (hconc s (hJ'J hs)).subset hballV (convex_ball _ _)) v w
    (fun j => (hw j).mono hsmallO)
    (fun j p hp => (hwp p (hsmallO hp) j).le)
    (fun p hp => hrep p (hsmallO hp))
    (hB.mono_set hsmallJV) φ hφ hφc hφV hφn

end DifferentialGeometry.CheegerGromovCompactness
