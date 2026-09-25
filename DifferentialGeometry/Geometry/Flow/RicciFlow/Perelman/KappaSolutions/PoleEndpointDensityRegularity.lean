import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointDensityWeakEquation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TensorNormFinrankNeZero
import DifferentialGeometry.Analysis.Parabolic.ClosedCell.ChartRegularity
import DifferentialGeometry.Analysis.Elliptic.MetricExtension.ChartCoefficients
import DifferentialGeometry.Analysis.Sobolev.Chart.Regularity

noncomputable section

open Filter Manifold MeasureTheory Set
open scoped ContDiff Manifold Matrix Topology

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

local notation "Z" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private theorem pullback_metric_weak_equation_of_ae_chart_representatives
    (g : ℝ → SmoothRiemannianMetric I M) (α : M)
    {Ω : Set Z} (hΩ : IsOpen Ω)
    (hΩt : closure Ω ⊆ chartTargetEuclid (I := I) α)
    (a b : ℝ) (u : ℝ × Z → ℝ) :
    let ν := (volume.restrict (Icc a b)).prod (volume.restrict Ω)
    let Ψ : Z → M := fun y => (extChartAt I α).symm ((toEuclidean (E := E)).symm y)
    let Q : ℝ × Z → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
      fun q => Matrix.of (fun i j => pullbackMetricCoefficients (g q.1) Ψ q.2
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
    ∀ (V : Lp ℝ 2 ν) (K : Fin (Module.finrank ℝ E) → Lp ℝ 2 ν),
      (V =ᵐ[ν] u) →
      (∀ i, K i =ᵐ[ν] fun q =>
        fderiv ℝ (fun y => u (q.1, y)) q.2 (EuclideanSpace.single i 1)) →
      (∀ φ : ℝ × Z → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω →
        (∫ q, densityOnEuclid (g q.1) α q.2 * V q * fderiv ℝ φ q (1, 0) ∂ν) =
          ∑ j, ∫ q, (∑ i, weightedInvGramOnEuclid (g q.1) α i j q.2 * K i q) *
            fderiv ℝ φ q (0, EuclideanSpace.single j 1) ∂ν) →
      ∀ φ : ℝ × Z → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ω →
        (∫ q, Real.sqrt (Q q).det * u q * fderiv ℝ φ q (1, 0)
          ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω)) =
          ∑ j, ∫ q, (∑ i, (Real.sqrt (Q q).det * (Q q)⁻¹ i j) *
            fderiv ℝ (fun y => u (q.1, y)) q.2 (EuclideanSpace.single i 1)) *
            fderiv ℝ φ q (0, EuclideanSpace.single j 1)
              ∂(volume.restrict (Icc a b)).prod (volume.restrict Ω) := by
  intro ν Ψ Q V K hV hK hweak φ hφ hcompact hsupport
  have hinterior : Ω ⊆ interior (chartTargetEuclid (I := I) α) :=
    interior_maximal (subset_closure.trans hΩt) hΩ
  have hmem : ∀ᵐ q ∂ν, q ∈ Icc a b ×ˢ Ω := by
    dsimp only [ν]
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Icc.prod hΩ.measurableSet)
  have hKall : ∀ᵐ q ∂ν, ∀ i, K i q =
      fderiv ℝ (fun y => u (q.1, y)) q.2 (EuclideanSpace.single i 1) :=
    Filter.eventually_all.mpr hK
  have hdensity : ∀ᵐ q ∂ν, densityOnEuclid (g q.1) α q.2 =
      Real.sqrt (Q q).det := by
    filter_upwards [hmem] with q hq
    exact densityOnEuclid_eq_sqrt_det_pullbackMetricCoefficients
      (g q.1) α (hinterior hq.2)
  have hcoefficient : ∀ᵐ q ∂ν, ∀ i j,
      weightedInvGramOnEuclid (g q.1) α i j q.2 =
        Real.sqrt (Q q).det * (Q q)⁻¹ i j := by
    filter_upwards [hmem] with q hq
    intro i j
    exact weightedInvGramOnEuclid_eq_sqrt_det_mul_inv_pullbackMetricCoefficients
      (g q.1) α (hinterior hq.2) i j
  have hleft :
      (∫ q, densityOnEuclid (g q.1) α q.2 * V q * fderiv ℝ φ q (1, 0) ∂ν) =
        ∫ q, Real.sqrt (Q q).det * u q * fderiv ℝ φ q (1, 0) ∂ν := by
    apply integral_congr_ae
    filter_upwards [hdensity, hV] with q hq hqV
    rw [hq, hqV]
  have hright (j : Fin (Module.finrank ℝ E)) :
      (∫ q, (∑ i, weightedInvGramOnEuclid (g q.1) α i j q.2 * K i q) *
        fderiv ℝ φ q (0, EuclideanSpace.single j 1) ∂ν) =
      ∫ q, (∑ i, (Real.sqrt (Q q).det * (Q q)⁻¹ i j) *
        fderiv ℝ (fun y => u (q.1, y)) q.2 (EuclideanSpace.single i 1)) *
        fderiv ℝ φ q (0, EuclideanSpace.single j 1) ∂ν := by
    apply integral_congr_ae
    filter_upwards [hcoefficient, hKall] with q hq hqK
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [hq i j, hqK i]
  calc
    (∫ q, Real.sqrt (Q q).det * u q * fderiv ℝ φ q (1, 0) ∂ν) =
        ∫ q, densityOnEuclid (g q.1) α q.2 * V q * fderiv ℝ φ q (1, 0) ∂ν :=
      hleft.symm
    _ = ∑ j, ∫ q, (∑ i, weightedInvGramOnEuclid (g q.1) α i j q.2 * K i q) *
        fderiv ℝ φ q (0, EuclideanSpace.single j 1) ∂ν :=
      hweak φ hφ hcompact hsupport
    _ = ∑ j, ∫ q, (∑ i, (Real.sqrt (Q q).det * (Q q)⁻¹ i j) *
        fderiv ℝ (fun y => u (q.1, y)) q.2 (EuclideanSpace.single i 1)) *
        fderiv ℝ φ q (0, EuclideanSpace.single j 1) ∂ν := by
      apply Finset.sum_congr rfl
      intro j _
      exact hright j

end DifferentialGeometry.Analysis.Parabolic

namespace DifferentialGeometry.Analysis.Sobolev.Chart

variable {P E F H M : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞}
  [IsManifold I n M]

private def productChartPushedRaw (α : M) (e : E ≃L[ℝ] F)
    (f : P × M → ℝ) : P × F → ℝ :=
  fun q => f (q.1, (extChartAt I α).symm (e.symm q.2))

private theorem contMDiffAt_productChart_coordinates
    {α x : M} (hx : x ∈ (extChartAt I α).source) (t : P) (e : E ≃L[ℝ] F) :
    ContMDiffAt ((𝓘(ℝ, P)).prod I) 𝓘(ℝ, P × F) n
      (fun q : P × M => (q.1, e (extChartAt I α q.2))) (t, x) := by
  have hα : ContMDiffAt I 𝓘(ℝ, E) n (extChartAt I α) x :=
    contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using hx)
  have he : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) n e (extChartAt I α x) :=
    contMDiffAt_iff_contDiffAt.mpr e.contDiff.contDiffAt
  have heα : ContMDiffAt I 𝓘(ℝ, F) n
      (fun y : M => e (extChartAt I α y)) x :=
    he.comp x hα
  have hsnd : ContMDiffAt (𝓘(ℝ, P).prod I) I n (Prod.snd : P × M → M) (t, x) :=
    contMDiffAt_snd
  have hsecond : ContMDiffAt (𝓘(ℝ, P).prod I) 𝓘(ℝ, F) n
      (fun q : P × M => e (extChartAt I α q.2)) (t, x) :=
    ContMDiffAt.comp (I := 𝓘(ℝ, P).prod I) (I' := I)
      (I'' := 𝓘(ℝ, F)) (f := (Prod.snd : P × M → M)) (t, x) heα hsnd
  exact contMDiffAt_fst.prodMk_space hsecond

private theorem contMDiffAt_productChart_pushedRaw
    {α x : M} (hx : x ∈ (extChartAt I α).source) (t : P) (e : E ≃L[ℝ] F)
    {f : P × M → ℝ}
    (hf : ContDiffAt ℝ n (productChartPushedRaw (I := I) α e f)
      (t, e (extChartAt I α x))) :
    ContMDiffAt ((𝓘(ℝ, P)).prod I) 𝓘(ℝ, ℝ) n f (t, x) := by
  have hcoords := contMDiffAt_productChart_coordinates (I := I) (n := n) hx t e
  have hraw : ContMDiffAt 𝓘(ℝ, P × F) 𝓘(ℝ, ℝ) n
      (productChartPushedRaw (I := I) α e f) (t, e (extChartAt I α x)) :=
    contMDiffAt_iff_contDiffAt.mpr hf
  have hcomp : ContMDiffAt ((𝓘(ℝ, P)).prod I) 𝓘(ℝ, ℝ) n
      (productChartPushedRaw (I := I) α e f ∘
        fun q : P × M => (q.1, e (extChartAt I α q.2))) (t, x) :=
    hraw.comp (t, x) hcoords
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [continuousAt_snd.preimage_mem_nhds
      ((isOpen_extChartAt_source α).mem_nhds hx)] with q hq
  simp only [Function.comp_apply, productChartPushedRaw, e.symm_apply_apply,
    (extChartAt I α).left_inv hq]

private theorem contMDiffAt_of_contDiffAt_productChartPushedRaw_of_mem_source
    {α x : M} (hx : x ∈ (extChartAt I α).source) (t : P) (e : E ≃L[ℝ] F)
    {f : P × M → ℝ}
    (hf : ContDiffAt ℝ n
      (fun q : P × F => f (q.1, (extChartAt I α).symm (e.symm q.2)))
      (t, e (extChartAt I α x))) :
    ContMDiffAt ((𝓘(ℝ, P)).prod I) 𝓘(ℝ, ℝ) n f (t, x) :=
  contMDiffAt_productChart_pushedRaw (I := I) hx t e hf

private theorem contMDiffAt_of_contDiffAt_toEuclidean_product_chart_of_mem_source
    [FiniteDimensional ℝ E] {α x : M} (hx : x ∈ (extChartAt I α).source) (t : P)
    {f : P × M → ℝ}
    (hf : ContDiffAt ℝ n
      (fun q : P × EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        f (q.1, (extChartAt I α).symm ((toEuclidean (E := E)).symm q.2)))
      (t, toEuclidean (E := E) (extChartAt I α x))) :
    ContMDiffAt ((𝓘(ℝ, P)).prod I) 𝓘(ℝ, ℝ) n f (t, x) :=
  contMDiffAt_of_contDiffAt_productChartPushedRaw_of_mem_source (I := I) hx t
    (toEuclidean (E := E)) hf

end DifferentialGeometry.Analysis.Sobolev.Chart

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H M : Type*}
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private theorem exists_compact_euclidean_chart_ball (x : M) :
    ∃ r : ℝ, 0 < r ∧
      let y := toEuclidean (E := E) (extChartAt I x x)
      let Ω := Metric.ball y r
      let K := (toEuclidean (E := E)).symm '' closure Ω
      let J := (extChartAt I x).symm '' K
      IsOpen Ω ∧ y ∈ Ω ∧ IsCompact (closure Ω) ∧
        K ⊆ (extChartAt I x).target ∧ IsCompact J ∧ x ∈ J ∧
        MapsTo (fun z => (extChartAt I x).symm ((toEuclidean (E := E)).symm z))
          (closure Ω) J ∧
        MapsTo (fun z => (extChartAt I x).symm ((toEuclidean (E := E)).symm z))
          Ω J ∧ J ⊆ (extChartAt I x).source := by
  let e := toEuclidean (E := E)
  let c := extChartAt I x
  let y := e (c x)
  let U := e.symm ⁻¹' c.target
  have hyc : c x ∈ c.target := mem_extChartAt_target x
  have hyU : y ∈ U := by
    change e.symm (e (c x)) ∈ c.target
    simpa only [e.symm_apply_apply] using hyc
  have hU : IsOpen U :=
    (isOpen_extChartAt_target x).preimage e.symm.continuous
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hyU)
  let Ω := Metric.ball y r
  let K := e.symm '' closure Ω
  let J := c.symm '' K
  have hΩc : IsCompact (closure Ω) :=
    (isCompact_closedBall y r).of_isClosed_subset isClosed_closure
      Metric.closure_ball_subset_closedBall
  have hK : K ⊆ c.target := by
    rintro z ⟨w, hw, rfl⟩
    exact hball (Metric.closure_ball_subset_closedBall hw)
  have hKc : IsCompact K := hΩc.image e.symm.continuous
  have hJc : IsCompact J :=
    hKc.image_of_continuousOn ((continuousOn_extChartAt_symm x).mono hK)
  have hyΩ : y ∈ Ω := Metric.mem_ball_self hr
  have hxJ : x ∈ J := by
    refine ⟨c x, ?_, c.left_inv (mem_extChartAt_source x)⟩
    refine ⟨y, subset_closure hyΩ, ?_⟩
    exact e.symm_apply_apply (c x)
  have hmap : MapsTo (fun z => c.symm (e.symm z)) (closure Ω) J := by
    intro z hz
    exact ⟨e.symm z, ⟨z, hz, rfl⟩, rfl⟩
  have hmaps : MapsTo (fun z => c.symm (e.symm z)) Ω J :=
    hmap.mono_left subset_closure
  have hJsource : J ⊆ c.source := by
    rintro z ⟨w, hw, rfl⟩
    exact c.map_target (hK hw)
  exact ⟨r, hr, Metric.isOpen_ball, hyΩ, hΩc, hK, hJc, hxJ, hmap, hmaps, hJsource⟩

end

namespace DifferentialGeometry.Analysis.Sobolev.Chart

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M]

private theorem contMDiffAt_of_contDiffOn_compact_chart
    (f : ℝ × M → ℝ) (x : M) {a c t : ℝ} (ht : t ∈ Ioo a c)
    (hlocal : ∀ Ω : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))),
      IsOpen Ω → IsCompact (closure Ω) →
      (toEuclidean (E := E)).symm '' closure Ω ⊆ (extChartAt I x).target →
      ∀ J : Set M, IsCompact J →
      MapsTo (extChartAt I x).symm ((toEuclidean (E := E)).symm '' closure Ω) J →
      ContDiffOn ℝ (⊤ : ℕ∞)
        (fun q : ℝ × EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          f (q.1, (extChartAt I x).symm ((toEuclidean (E := E)).symm q.2)))
        (Ioo a c ×ˢ Ω)) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ f (t, x) := by
  obtain ⟨r, _, hΩ, hyΩ, hΩc, hΩt, hJ, _, _, _, _⟩ :=
    exists_compact_euclidean_chart_ball (I := I) x
  let y := toEuclidean (E := E) (extChartAt I x x)
  let Ω : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) := Metric.ball y r
  let J := (extChartAt I x).symm '' ((toEuclidean (E := E)).symm '' closure Ω)
  have hΩJ : MapsTo (extChartAt I x).symm
      ((toEuclidean (E := E)).symm '' closure Ω) J :=
    fun z hz => ⟨z, hz, rfl⟩
  have hs : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        f (q.1, (extChartAt I x).symm ((toEuclidean (E := E)).symm q.2)))
      (Ioo a c ×ˢ Ω) :=
    hlocal Ω hΩ hΩc hΩt J hJ hΩJ
  have hsAt : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q : ℝ × EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        f (q.1, (extChartAt I x).symm ((toEuclidean (E := E)).symm q.2))) (t, y) :=
    hs.contDiffAt ((isOpen_Ioo.prod hΩ).mem_nhds ⟨ht, hyΩ⟩)
  exact contMDiffAt_of_contDiffAt_toEuclidean_product_chart_of_mem_source
    (I := I) (n := ∞) (f := f) (mem_extChartAt_source x) t hsAt

end DifferentialGeometry.Analysis.Sobolev.Chart

private theorem locallyLipschitzOn_comp_lipschitzWith
    {X Y Z : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y] [PseudoEMetricSpace Z]
    {S : Set X} {T : Set Y} {f : Y → Z} {g : X → Y} {C : NNReal}
    (hf : LocallyLipschitzOn T f) (hg : LipschitzWith C g) (hmap : Set.MapsTo g S T) :
    LocallyLipschitzOn S (f ∘ g) := by
  apply locallyLipschitzOn_iff_restrict.mpr
  exact hf.restrict.comp (hg.lipschitzOnWith.mapsToRestrict hmap).locallyLipschitz

namespace DifferentialGeometry.CheegerGromovCompactness

open Bundle Filter _root_.Manifold MeasureTheory Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open CanonicalNeighborhood
open DifferentialGeometry.Analysis.Sobolev.Euclidean
  (spatial_fderiv_exp_gaussian_normalization_ae_of_locallyLipschitzOn)
open DifferentialGeometry.Analysis.Parabolic
  (exists_lp_weak_equation_exp_gaussian_of_chartResidual_eq_zero
    contDiffOn_of_locallyLipschitzOn_inverse_chart_metric_weak_equation
    pullback_metric_weak_equation_of_ae_chart_representatives)
open DifferentialGeometry.Analysis.Sobolev.Chart
  (contMDiffAt_of_contDiffOn_compact_chart)
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
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
  PointedRiemannianManifold.t2TangentBundle

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

local notation "U" => poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
local notation "Y" => poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma

namespace HalfLineMetricConvergenceData

local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private local instance : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ E)) → ℝ)

theorem contDiffOn_poleEndpoint_redDensity_limit_time_chart_of_chartResidual_eq_zero
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    (hR : RiemannianMetricComplete R)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J) {A a c : ℝ} (ha : 1 < a)
    (hbase : ∀ᶠ k in atTop, redLength ((U).term (phi (co.φ k))).S 0 p
      (q (phi (co.φ k))) 1 ≤ A)
    (rho : ℕ → ℕ) (hrho : Tendsto rho atTop atTop)
    (ell : P.M × ℝ → ℝ)
    (hconv : ∀ y ∈ J, ∀ t ∈ Icc a c,
      Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) y) t) atTop (𝓝 (ell (y, t))))
    (x : P.M) {Ω : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩt : (toEuclidean (E := E)).symm '' closure Ω ⊆ (extChartAt I x).target)
    (hΩJ : MapsTo (extChartAt I x).symm ((toEuclidean (E := E)).symm '' closure Ω) J) :
    let f := fun z : ℝ × E => ell ((extChartAt I x).symm z.2, z.1)
    let u := fun z : ℝ × E => Real.exp (-f z -
      (Module.finrank ℝ E : ℝ) / 2 * Real.log z.1 -
      (Module.finrank ℝ E : ℝ) / 2 * Real.log (4 * Real.pi))
    let uV := fun v : ℝ × EuStd => u (v.1, (toEuclidean (E := E)).symm v.2)
    (∀ ψ : ℝ × E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a c ×ˢ ((toEuclidean (E := E)) ⁻¹' Ω) →
      (∫ z, chartDensity (co.gInf (1 - z.1)) x ((extChartAt I x).symm z.2) * u z *
        (deriv (fun t => ψ (t, z.2)) z.1 +
          chartGradientBilin (co.gInf (1 - z.1)) x ((extChartAt I x).symm z.2)
            (fderiv ℝ (fun y => f (z.1, y)) z.2)
            (fderiv ℝ (fun y => ψ (z.1, y)) z.2))
        ∂(volume.restrict (Ioc a c)).prod
          ((modelHaar (E := E)).restrict ((toEuclidean (E := E)) ⁻¹' Ω))) = 0) →
    ContDiffOn ℝ (⊤ : ℕ∞) uV (Ioo a c ×ˢ Ω) := by
  intro f u uV hresidual
  obtain ⟨V, K, hV, hK, _, _, hweak⟩ :=
    exists_lp_weak_equation_poleEndpoint_redDensity_limit_of_chartResidual_eq_zero
      F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ ha hbase
      rho hrho ell hconv x hΩ hΩc hΩt hΩJ hresidual
  have hΩtV : closure Ω ⊆ chartTargetEuclid (I := I) x := by
    intro y hy
    exact ⟨(toEuclidean (E := E)).symm y, hΩt ⟨y, hy, rfl⟩,
      (toEuclidean (E := E)).apply_symm_apply y⟩
  have hweakActual :=
    pullback_metric_weak_equation_of_ae_chart_representatives
      (fun t => co.gInf (1 - t)) x hΩ hΩtV a c uV V K hV hK hweak
  have hchart := locallyLipschitzOn_poleEndpoint_redDensity_limit_time_chart
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ ha.le hbase
      rho hrho ell hconv x hΩt hΩJ
  let T : ℝ × EuStd → ℝ × E := fun v => (v.1, (toEuclidean (E := E)).symm v.2)
  have hT : LipschitzWith (max 1 ‖(toEuclidean (E := E)).symm.toContinuousLinearMap‖₊) T := by
    simpa only [mul_one, T, Function.comp_def] using
      (LipschitzWith.prod_fst : LipschitzWith 1 (Prod.fst : ℝ × EuStd → ℝ)).prodMk
        ((toEuclidean (E := E)).symm.lipschitz.comp
          (LipschitzWith.prod_snd : LipschitzWith 1 (Prod.snd : ℝ × EuStd → EuStd)))
  have hmaps : MapsTo T (Icc a c ×ˢ closure Ω)
      (Icc a c ×ˢ ((toEuclidean (E := E)).symm '' closure Ω)) :=
    fun v hv => ⟨hv.1, ⟨v.2, hv.2, rfl⟩⟩
  have huClosure : LocallyLipschitzOn (Icc a c ×ˢ closure Ω) uV := by
    simpa only [Function.comp_def, T, f, u, uV] using
      locallyLipschitzOn_comp_lipschitzWith hchart hT hmaps
  have hu : LocallyLipschitzOn (Icc a c ×ˢ Ω) uV :=
    huClosure.mono (prod_mono Subset.rfl subset_closure)
  let Dτ := RealTimeInterval.openInfinite 1 a ha
  have hYreg : Iio 0 ⊆ (Y).D.regular := by
    change Iio 0 ⊆ ancientTimeInterval.regular
    rw [ancientTimeInterval_regular]
  have hg : MetricFamilySmoothOn (I := I) Dτ (fun t => co.gInf (1 - t)) :=
    co.metric_smooth_time_sub (Φ := Phi) hYreg 1 (fun _ ht => ht)
  have hinterval : Icc a c ⊆ Dτ.regular := fun _ ht => ha.trans_le ht.1
  have hΩtarget : ∀ y ∈ Ω,
      (toEuclidean (E := E)).symm y ∈ (extChartAt I x).target :=
    fun y hy => hΩt ⟨y, subset_closure hy, rfl⟩
  have hdim0 : Module.finrank ℝ E ≠ 0 := by
    obtain ⟨t, ht, y, hy⟩ := (hancient 0).notFlat
    exact DifferentialGeometry.Tensor0SBundle.finrank_ne_zero_of_normSq0S_ne_zero
      (((U).term 0).S.base.metric t) y (by norm_num : 0 < 4)
      (((U).term 0).S.base.rm04 t y) hy
  have hdim : Module.finrank ℝ E = (Module.finrank ℝ E - 1) + 1 := by omega
  exact contDiffOn_of_locallyLipschitzOn_inverse_chart_metric_weak_equation
      hdim Dτ (fun t => co.gInf (1 - t)) hg x Ω hΩ hΩtarget hinterval uV hu hweakActual

private theorem contMDiffOn_poleEndpoint_redDensity_limit_of_tendsto_at_chartResidual_eq_zero
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    (hR : RiemannianMetricComplete R)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {A : ℝ}
    (hbase : ∀ᶠ k in atTop, redLength ((U).term (phi (co.φ k))).S 0 p
      (q (phi (co.φ k))) 1 ≤ A)
    (rho : ℕ → ℕ) (hrho : Tendsto rho atTop atTop)
    (ell : P.M × ℝ → ℝ)
    (hconv : ∀ y : P.M, ∀ t ∈ Ici (1 : ℝ),
      Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) y) t) atTop (𝓝 (ell (y, t))))
    (hchartResidual : ∀ (x : P.M) (Ω : Set EuStd),
      IsOpen Ω → IsCompact (closure Ω) →
      (toEuclidean (E := E)).symm '' closure Ω ⊆ (extChartAt I x).target →
      ∀ (a c : ℝ), 1 < a → a < c →
      let f := fun z : ℝ × E => ell ((extChartAt I x).symm z.2, z.1)
      let u := fun z : ℝ × E => Real.exp (-f z -
        (Module.finrank ℝ E : ℝ) / 2 * Real.log z.1 -
        (Module.finrank ℝ E : ℝ) / 2 * Real.log (4 * Real.pi))
      ∀ ψ : ℝ × E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ Ioo a c ×ˢ ((toEuclidean (E := E)) ⁻¹' Ω) →
        (∫ z, chartDensity (co.gInf (1 - z.1)) x ((extChartAt I x).symm z.2) * u z *
          (deriv (fun t => ψ (t, z.2)) z.1 +
            chartGradientBilin (co.gInf (1 - z.1)) x ((extChartAt I x).symm z.2)
              (fderiv ℝ (fun y => f (z.1, y)) z.2)
              (fderiv ℝ (fun y => ψ (z.1, y)) z.2))
          ∂(volume.restrict (Ioc a c)).prod
            ((modelHaar (E := E)).restrict ((toEuclidean (E := E)) ⁻¹' Ω))) = 0) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × P.M => Real.exp (-ell (z.2, z.1) -
        (Module.finrank ℝ E : ℝ) / 2 * Real.log z.1 -
        (Module.finrank ℝ E : ℝ) / 2 * Real.log (4 * Real.pi)))
      (Ioi (1 : ℝ) ×ˢ (univ : Set P.M)) := by
  let fM : ℝ × P.M → ℝ := fun z => Real.exp (-ell (z.2, z.1) -
    (Module.finrank ℝ E : ℝ) / 2 * Real.log z.1 -
    (Module.finrank ℝ E : ℝ) / 2 * Real.log (4 * Real.pi))
  intro z hz
  let a := (1 + z.1) / 2
  let c := z.1 + 1
  have hzTime : 1 < z.1 := hz.1
  have ha : 1 < a := by dsimp [a]; linarith only [hzTime]
  have ht : z.1 ∈ Ioo a c := by
    constructor
    · dsimp [a]; linarith only [hzTime]
    · dsimp [c]; exact lt_add_one _
  refine (contMDiffAt_of_contDiffOn_compact_chart (I := I) fM z.2 ht ?_).contMDiffWithinAt
  intro Ω hΩ hΩc hΩt J hJ hΩJ
  have hconvLocal : ∀ x ∈ J, ∀ t ∈ Icc a c,
      Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) x) t) atTop (𝓝 (ell (x, t))) :=
    fun x _ t ht => hconv x t (ha.le.trans ht.1)
  exact contDiffOn_poleEndpoint_redDensity_limit_time_chart_of_chartResidual_eq_zero
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ ha hbase
    rho hrho ell hconvLocal z.2 hΩ hΩc hΩt hΩJ
    (hchartResidual z.2 Ω hΩ hΩc hΩt a c ha (ht.1.trans ht.2))

theorem contMDiffOn_poleEndpoint_redDensity_limit_of_chartResidual_eq_zero
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    (hR : RiemannianMetricComplete R)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {A : ℝ}
    (hbase : ∀ᶠ k in atTop, redLength ((U).term (phi (co.φ k))).S 0 p
      (q (phi (co.φ k))) 1 ≤ A)
    (rho : ℕ → ℕ) (hrho : StrictMono rho) (ellC : C(P.M × Ici (1 : ℝ), ℝ))
    (hconv : TendstoLocallyUniformly
      (fun k (z : P.M × Ici (1 : ℝ)) =>
        redLength ((U).term (phi (co.φ (rho k)))).S 0 p
          (Phi.map (co.φ (rho k)) z.1) z.2) ellC atTop)
    (ell : P.M × ℝ → ℝ)
    (hagree : ∀ (y : P.M) (t : ℝ) (ht : 1 ≤ t), ell (y, t) = ellC (y, ⟨t, ht⟩))
    (hchartResidual : ∀ (x : P.M) (Ω : Set EuStd),
      IsOpen Ω → IsCompact (closure Ω) →
      (toEuclidean (E := E)).symm '' closure Ω ⊆ (extChartAt I x).target →
      ∀ (a c : ℝ), 1 < a → a < c →
      let f := fun z : ℝ × E => ell ((extChartAt I x).symm z.2, z.1)
      let u := fun z : ℝ × E => Real.exp (-f z -
        (Module.finrank ℝ E : ℝ) / 2 * Real.log z.1 -
        (Module.finrank ℝ E : ℝ) / 2 * Real.log (4 * Real.pi))
      ∀ ψ : ℝ × E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ Ioo a c ×ˢ ((toEuclidean (E := E)) ⁻¹' Ω) →
        (∫ z, chartDensity (co.gInf (1 - z.1)) x ((extChartAt I x).symm z.2) * u z *
          (deriv (fun t => ψ (t, z.2)) z.1 +
            chartGradientBilin (co.gInf (1 - z.1)) x ((extChartAt I x).symm z.2)
              (fderiv ℝ (fun y => f (z.1, y)) z.2)
              (fderiv ℝ (fun y => ψ (z.1, y)) z.2))
          ∂(volume.restrict (Ioc a c)).prod
            ((modelHaar (E := E)).restrict ((toEuclidean (E := E)) ⁻¹' Ω))) = 0) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × P.M => Real.exp (-ell (z.2, z.1) -
        (Module.finrank ℝ E : ℝ) / 2 * Real.log z.1 -
        (Module.finrank ℝ E : ℝ) / 2 * Real.log (4 * Real.pi)))
      (Ioi (1 : ℝ) ×ˢ (univ : Set P.M)) := by
  have hconvPointwise : ∀ y : P.M, ∀ t ∈ Ici (1 : ℝ),
      Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) y) t) atTop (𝓝 (ell (y, t))) := by
    intro y t ht
    have hpt := hconv.tendstoLocallyUniformlyOn.tendsto_at
      (mem_univ (y, (⟨t, ht⟩ : Ici (1 : ℝ))))
    rw [hagree y t ht]
    exact hpt
  exact contMDiffOn_poleEndpoint_redDensity_limit_of_tendsto_at_chartResidual_eq_zero
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hbase
    rho hrho.tendsto_atTop ell hconvPointwise hchartResidual

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness

end
