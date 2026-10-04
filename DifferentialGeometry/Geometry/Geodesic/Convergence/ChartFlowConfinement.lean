import DifferentialGeometry.Geometry.Geodesic.Convergence.ChartMetricFlow
import DifferentialGeometry.Geometry.Geodesic.Convergence.ChartFirstExit

/-!
# Actual metric-flow convergence without approximating chart confinement

Native covariant metric convergence gives the actual chart phase fields. The first-exit kernel
then derives confinement and position/velocity convergence for the original geodesic flows.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry (pullbackMetricCoefficients)
open DifferentialGeometry.Analysis.ODE.GeodesicLimits
open DifferentialGeometry.MetricKoszul

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance phaseDual : DifferentialGeometry.ContinuousDualEquiv E :=
  IsCoercive.continuousDualEquivOfFiniteDimensional
private local instance phaseDualGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance phaseDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
private local instance phaseBilinearGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance phaseBilinearSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private local instance phaseGammaGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance phaseGammaSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace

private theorem metricPhase_uniform_on_compact
    {U : Set E} (hU : IsOpen U)
    (b : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ) (bInf : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hb : ∀ i, ContDiffOn ℝ 1 (b i) U) (hbInf : ContDiffOn ℝ 1 bInf U)
    (hco : ∀ x ∈ U, IsCoercive (bInf x))
    (hconv : ∀ C : Set E, IsCompact C → C ⊆ U → MapCPConvergenceOn C 1 b bInf)
    {C : Set (E × E)} (hC : IsCompact C) (hCU : C ⊆ U ×ˢ univ) :
    TendstoUniformlyOn (fun i => metricSpray (b i)) (metricSpray bInf) atTop C := by
  let Gamma (B : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E) :=
    raisedKoszulOp (B x) (fderiv ℝ B x)
  have hfstC : IsCompact (Prod.fst '' C) := hC.image continuous_fst
  have hfstU : Prod.fst '' C ⊆ U := by
    rintro x ⟨y, hy, rfl⟩
    exact (hCU hy).1
  have hGamma := tendstoUniformlyOn_raisedKoszulOp_of_mapCPConvergenceOn hU hfstC hfstU
    b bInf hb hbInf (fun x hx => hco x (hfstU hx)) (hconv _ hfstC hfstU)
  have hGammaC : TendstoUniformlyOn (fun (i : ℕ) (y : E × E) => Gamma (b i) y.1)
      (fun y => Gamma bInf y.1) atTop C := by
    rw [Metric.tendstoUniformlyOn_iff] at hGamma ⊢
    intro epsilon hepsilon
    filter_upwards [hGamma epsilon hepsilon] with i hi y hy
    exact hi y.1 (mem_image_of_mem Prod.fst hy)
  have hsnd : TendstoUniformlyOn (fun _i : ℕ => fun y : E × E => y.2)
      Prod.snd atTop C := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro epsilon hepsilon
    exact Eventually.of_forall (fun _i _y _hy => by simpa using hepsilon)
  have hGammaCont := continuousOn_raisedKoszulOp_fderiv hU hfstU hbInf
    (fun x hx => hco x (hfstU hx))
  have hK : IsCompact ((Gamma bInf '' (Prod.fst '' C)) ×ˢ (Prod.snd '' C)) :=
    (hfstC.image_of_continuousOn hGammaCont).prod (hC.image continuous_snd)
  let Psi : (E →L[ℝ] E →L[ℝ] E) × E → E × E := fun y => (y.2, -(y.1 y.2 y.2))
  have hPsi : Continuous Psi :=
    continuous_snd.prodMk ((continuous_fst.clm_apply continuous_snd).clm_apply continuous_snd).neg
  exact (tendstoUniformlyOn_prodMk hGammaC hsnd).comp_continuousAt_of_isCompact hK
    (fun y hy => ⟨mem_image_of_mem (Gamma bInf) (mem_image_of_mem Prod.fst hy),
      mem_image_of_mem Prod.snd hy⟩) (fun y _hy => hPsi.continuousAt)

theorem geodesicFlow_chart_confinement_of_metricCP
    (g : ℕ → SmoothRiemannianMetric I M) (gInf gRef : SmoothRiemannianMetric I M)
    (hconv : ∀ C : Set M, IsCompact C → MetricCPConvergenceOn C 1 g gInf gRef)
    (q : TangentBundle I M) (p : ℕ → TangentBundle I M) (pInf : TangentBundle I M)
    {a b : ℝ} (hab : a ≤ b)
    (hdom : ∀ i, ∀ t ∈ Icc a b, (p i, t) ∈ (g i).geodesicFlowDomain)
    (hdomInf : ∀ t ∈ Icc a b, (pInf, t) ∈ gInf.geodesicFlowDomain)
    (hchartInf : ∀ t ∈ Icc a b,
      (gInf.geodesicFlow pInf t).proj ∈ (chartAt H q.proj).source)
    (hinit : Tendsto (fun i => (g i).geodesicFlow (p i) a)
      atTop (𝓝 (gInf.geodesicFlow pInf a))) :
    (∀ᶠ i in atTop, ∀ t ∈ Icc a b,
      ((g i).geodesicFlow (p i) t).proj ∈ (chartAt H q.proj).source) ∧
    TendstoUniformlyOn (fun i t => extChartAt I.tangent q ((g i).geodesicFlow (p i) t))
      (fun t => extChartAt I.tangent q (gInf.geodesicFlow pInf t)) atTop (Icc a b) := by
  let U := (extChartAt I q.proj).target
  have hU : IsOpen U := isOpen_extChartAt_target q.proj
  let e :=
    (DifferentialGeometry.PartialDiffeomorph.extChartAt I.tangent ∞ q).toOpenPartialHomeomorph
  let coeff (G : SmoothRiemannianMetric I M) :=
    pullbackMetricCoefficients G (extChartAt I q.proj).symm
  have hb (G : SmoothRiemannianMetric I M) : ContDiffOn ℝ ∞ (coeff G) U :=
    contDiffOn_pullback_metric_coefficients G hU (contMDiffOn_extChartAt_symm q.proj)
  have hco : ∀ x ∈ U, IsCoercive (coeff gInf x) := by
    intro x hx
    apply DifferentialGeometry.Analysis.isCoercive_of_pos_diagonal
    intro v hv
    apply pullbackMetricCoefficients_pos gInf
    · let Phi := (DifferentialGeometry.PartialDiffeomorph.extChartAt I ∞ q.proj).symm
      exact (Phi.isLocalDiffeomorphAt _ _ _ hx
        |>.mfderivToContinuousLinearEquiv (by simp)).injective
    · exact hv
  have hc : ∀ C : Set E, IsCompact C → C ⊆ U → MapCPConvergenceOn C 1
      (fun i => coeff (g i)) (coeff gInf) := by
    intro C hC hCU
    apply mapCPConvergence_chartBilinear_of_metricCP g gInf gRef q.proj hC hCU 1
    exact hconv _ (hC.image_of_continuousOn
      ((continuousOn_extChartAt_symm q.proj).mono hCU))
  have heTarget : e.target ⊆ U ×ˢ univ := by
    change (extChartAt I.tangent q).target ⊆ U ×ˢ univ
    rw [FiberBundle.extChartAt_target]
    exact fun x hx => ⟨hx.1.1, hx.2⟩
  have heSource (x : TangentBundle I M) : x ∈ e.source ↔
      x.proj ∈ (chartAt H q.proj).source := by
    change x ∈ (extChartAt I.tangent q).source ↔ _
    rw [extChartAt_source, TangentBundle.mem_chart_source_iff]
  let gamma (i : ℕ) := (g i).geodesicFlow (p i)
  let gammaInf := gInf.geodesicFlow pInf
  have hcontinuous : ∀ i, ContinuousOn (gamma i) (Icc a b) := by
    intro i t ht
    exact ((g i).isMIntegralCurveOn_geodesicFlow (r := ⊤) le_top (p i) t
      (hdom i t ht)).1.mono (fun s hs => hdom i s hs)
  have hsourceInf : MapsTo gammaInf (Icc a b) e.source :=
    fun t ht => (heSource _).mpr (hchartInf t ht)
  have hderiv (G : SmoothRiemannianMetric I M) (v : TangentBundle I M) (t : ℝ)
      (ht : (v, t) ∈ G.geodesicFlowDomain) (hsource : G.geodesicFlow v t ∈ e.source) :
      HasDerivWithinAt (e ∘ G.geodesicFlow v)
        (metricSpray (coeff G) (e (G.geodesicFlow v t))) (Icc a b) t :=
    (G.hasDerivAt_geodesicFlow_chart (r := ⊤) le_top ht q
      ((heSource _).mp hsource)).hasDerivWithinAt
  have hfield : ContDiffOn ℝ 1 (metricSpray (coeff gInf)) e.target :=
    ((metricSpray_contDiffOn hU (hb gInf) hco).of_le (by simp)).mono heTarget
  have hfieldConv : ∀ C : Set (E × E), IsCompact C → C ⊆ e.target →
      TendstoUniformlyOn (fun i => metricSpray (coeff (g i)))
        (metricSpray (coeff gInf)) atTop C := by
    intro C hC hCe
    exact metricPhase_uniform_on_compact hU (fun i => coeff (g i)) (coeff gInf)
      (fun i => (hb (g i)).of_le (by simp)) ((hb gInf).of_le (by simp)) hco hc hC
      (hCe.trans heTarget)
  have hstageODE := fun i t ht hs => hderiv (g i) (p i) t (hdom i t ht) hs
  have hlimitODE := fun t ht => hderiv gInf pInf t (hdomInf t ht) (hsourceInf ht)
  have hstay := eventually_mapsTo_chart_of_coordinate_ODE e hab gamma gammaInf
    (fun i => metricSpray (coeff (g i))) (metricSpray (coeff gInf)) hcontinuous
    hsourceInf hstageODE hlimitODE hfield hfieldConv hinit
  refine ⟨?_, tendstoUniformlyOn_chart_of_coordinate_ODE e hab gamma gammaInf
    (fun i => metricSpray (coeff (g i))) (metricSpray (coeff gInf)) hcontinuous
      hsourceInf hstageODE hlimitODE hfield hfieldConv hinit⟩
  filter_upwards [hstay] with i hi t ht
  exact (heSource _).mp (hi ht)


theorem realZero_geodesicFlow_chart_confinement {T : ℝ} (hT : 0 ≤ T) :
    let g := euclideanMetric (E := ℝ)
    let p : TangentBundle 𝓘(ℝ, ℝ) ℝ := ⟨0, 0⟩
    (∀ᶠ _i : ℕ in atTop, ∀ t ∈ Icc 0 T,
      (g.geodesicFlow p t).proj ∈ (chartAt ℝ p.proj).source) ∧
    TendstoUniformlyOn
      (fun _i : ℕ => fun t => extChartAt (𝓘(ℝ, ℝ)).tangent p (g.geodesicFlow p t))
      (fun t => extChartAt (𝓘(ℝ, ℝ)).tangent p (g.geodesicFlow p t)) atTop (Icc 0 T) := by
  let g := euclideanMetric (E := ℝ)
  let p : TangentBundle 𝓘(ℝ, ℝ) ℝ := ⟨0, 0⟩
  have hdom (t : ℝ) : (p, t) ∈ g.geodesicFlowDomain :=
    g.mem_geodesicFlowDomain_zeroSection 0 t
  have hchart (t : ℝ) : (g.geodesicFlow p t).proj ∈ (chartAt ℝ p.proj).source := by
    simp
  exact geodesicFlow_chart_confinement_of_metricCP (fun _i : ℕ => g) g g
    (fun C _hC epsilon hepsilon => ⟨0, fun _i _hi => by
      rw [metricDerivNormSupOn_self]; exact hepsilon⟩) p (fun _i : ℕ => p) p hT
    (fun _i t _ht => hdom t) (fun t _ht => hdom t)
    (fun t _ht => hchart t) tendsto_const_nhds

end DifferentialGeometry.Geometry.Riemannian.Geodesic
