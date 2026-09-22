import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointTerminalFirstDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.ClosedHalfLineSolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.ClosedRegularity
import DifferentialGeometry.Geometry.Metric.Family.Regularity.JointDifferentialOperator
import DifferentialGeometry.Geometry.Metric.RicciSoliton.HamiltonNormalizationLimit


noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Bundle Filter _root_.Manifold Set
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology ENNReal BigOperators

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)}

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

namespace HalfLineMetricConvergenceData

private theorem tendsto_chartInvGramMatrix_and_scalar_at_zero
    {X : PointedFlowSeq.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
    (Phi : PointedCGHMaps X P subseq) {R : SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hcarrier : X.D.carrier = Iic 0) (hregular : Iio 0 ⊆ X.D.regular)
    (α : P.M) {x : P.M} (hx : x ∈ (chartAt H α).source)
    {a : ℝ} (ha : a < 0) (t : ℕ → ℝ)
    (ht : ∀ n, t n ∈ Icc a 0) (htend : Tendsto t atTop (𝓝 0)) :
    (∀ i j : Fin (Module.finrank ℝ E),
      Tendsto (fun n => chartInvGramMatrix (co.gInf (t n)) α x i j) atTop
        (𝓝 (chartInvGramMatrix (co.gInf 0) α x i j))) ∧
      Tendsto (fun n => metricScalarAt (co.gInf (t n)) x) atTop
        (𝓝 (metricScalarAt (co.gInf 0) x)) := by
  let S : SolutionOn (I := I) (M := P.M) X.D := { base := { metric := co.gInf } }
  have hS : IsSolutionOn S := co.isSolutionOn Phi hcarrier hregular
  have hslab : Icc (a - 1) 0 ⊆ X.D.carrier := by
    rw [hcarrier]
    exact Icc_subset_Iic_self
  have hreg : Ioo (a - 1) 0 ⊆ X.D.regular := Ioo_subset_Iio_self.trans hregular
  have hmet :=
    DifferentialGeometry.PDE.RicciFlow.solution_metricCLMSection_contMDiffOn_closed
      S hS
    (sub_lt_self a zero_lt_one) ha hslab hreg
  have hxsrc : x ∈ (extChartAt I α).source := by
    simpa only [extChartAt_source] using hx
  have hxint : extChartAt I α x ∈ interior (extChartAt I α).target := by
    rw [(isOpen_extChartAt_target (I := I) α).interior_eq]
    exact (extChartAt I α).map_source hxsrc
  have hzero : (0 : ℝ) ∈ Icc a 0 := ⟨ha.le, le_rfl⟩
  constructor
  · intro i j
    have hc := chartInvGramOnE_continuousOn_of_contMDiffOn co.gInf hmet α i j
    have hpath : Tendsto (fun n => (t n, extChartAt I α x)) atTop
        (𝓝[Icc a 0 ×ˢ interior (extChartAt I α).target] (0, extChartAt I α x)) :=
      tendsto_nhdsWithin_iff.mpr ⟨htend.prodMk_nhds tendsto_const_nhds,
        Eventually.of_forall fun n => ⟨ht n, hxint⟩⟩
    have hh := (hc (0, extChartAt I α x) ⟨hzero, hxint⟩).tendsto.comp hpath
    simpa only [Function.comp_def, chartInvGramOnE_def,
      (extChartAt I α).left_inv hxsrc] using hh
  · have hzeroD : (0 : ℝ) ∈ X.D.carrier := by
      rw [hcarrier]
      exact (le_rfl : (0 : ℝ) ≤ 0)
    have hpath : Tendsto (fun n => (t n, x)) atTop
        (𝓝[X.D.carrier ×ˢ (univ : Set P.M)] (0, x)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨htend.prodMk_nhds tendsto_const_nhds, Eventually.of_forall fun n => ?_⟩
      refine ⟨?_, mem_univ x⟩
      rw [hcarrier]
      exact (ht n).2
    have hscalar : ContinuousOn
        (fun z : ℝ × P.M => metricScalarAt (co.gInf z.1) z.2)
        (X.D.carrier ×ˢ (univ : Set P.M)) := hS.scalarCont
    have hlimit := (hscalar (0, x) ⟨hzeroD, mem_univ x⟩).tendsto.comp hpath
    exact hlimit

section PoleEndpoint

variable {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)
  (hcar : D.carrier = Iic 0) (hreg : D.regular = Iio 0)
  (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
  (hsigma : ∀ i, 0 < tau i + b) {phi : ℕ → ℕ}

private local instance : TopologicalSpace F.M := F.topology
private local instance : ChartedSpace H F.M := F.charted
private local instance : IsManifold I ∞ F.M := F.smooth
private local instance : SigmaCompactSpace F.M := F.sigmaCompact
private local instance : T2Space F.M := F.t2

local notation "U" => poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
local notation "Y" => poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
local notation "θ" => (fun n : ℕ => (1 : ℝ) + 1 / ((n : ℝ) + 1))

theorem poleEndpoint_redLength_limit_terminal_hamilton
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
    (hconv : ∀ y : P.M, ∀ t ∈ Icc 1 2,
      Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) y) t) atTop (𝓝 (ell (y, t))))
    (hsmooth : ∀ n : ℕ, ContMDiff I 𝓘(ℝ) ∞ (fun x => ell (x, θ n)))
    (hsol : ∀ n : ℕ, gradientRicciSoliton (co.gInf (1 - θ n))
      (⟨fun x => ell (x, θ n), hsmooth n⟩ : C^∞⟮I, P.M; ℝ⟯) (1 / θ n))
    (hnormal : ∀ n : ℕ, ∀ x : P.M,
      metricScalarAt (co.gInf (1 - θ n)) x +
        normGradSqFun (co.gInf (1 - θ n)) (fun x => ell (x, θ n)) x =
          (1 / θ n) * ell (x, θ n)) :
    ∀ x : P.M, metricScalarAt (co.gInf 0) x +
      normGradSqFun (co.gInf 0) (fun x => ell (x, 1)) x = ell (x, 1) := by
  intro x
  classical
  let z : E := extChartAt I x x
  have hzt : z ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source (mem_extChartAt_source x)
  obtain ⟨rOut, hrOut, hWt⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    ((isOpen_extChartAt_target (I := I) x).mem_nhds hzt)
  let J : Set P.M := (extChartAt I x).symm '' Metric.closedBall z rOut
  have hJ : IsCompact J := (isCompact_closedBall z rOut).image_of_continuousOn
    ((continuousOn_extChartAt_symm (I := I) x).mono hWt)
  have hWJ : MapsTo (extChartAt I x).symm (Metric.closedBall z rOut) J :=
    fun y hy => mem_image_of_mem _ hy
  have hconvJ : ∀ y ∈ J, ∀ t ∈ Icc 1 2,
      Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) y) t) atTop (𝓝 (ell (y, t))) :=
    fun y _ t ht => hconv y t ht
  obtain ⟨hdiff, hD⟩ := poleEndpoint_redLength_limit_chart_terminal_fderiv
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ hbase
      rho hrho ell hconvJ hsmooth hsol x z
      (r := rOut / 4) (rMid := rOut / 2) (rOut := rOut)
      (by linarith) (by linarith) hWt hWJ
  have hzsmall : z ∈ Metric.ball z (rOut / 4) := Metric.mem_ball_self (by positivity)
  have hzmid : z ∈ Metric.ball z (rOut / 2) := Metric.mem_ball_self (by positivity)
  have hzclosed : z ∈ Metric.closedBall z rOut := Metric.mem_closedBall_self hrOut.le
  have hθpos (n : ℕ) : 1 < θ n := by
    change 1 < 1 + 1 / ((n : ℝ) + 1)
    have h : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have hθband (n : ℕ) : θ n ∈ Icc (1 : ℝ) 2 := by
    refine ⟨(hθpos n).le, ?_⟩
    have hdiv : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 :=
      (div_le_one (by positivity)).mpr (by
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith)
    change 1 + 1 / ((n : ℝ) + 1) ≤ 2
    linarith
  have hθlim : Tendsto θ atTop (𝓝 (1 : ℝ)) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := (1 : ℝ))).add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have ht : ∀ n : ℕ, 1 - θ n ∈ Icc (-1 : ℝ) 0 := by
    intro n
    obtain ⟨hlo, hhi⟩ := hθband n
    constructor <;> linarith
  have htend : Tendsto (fun n => 1 - θ n) atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self] using (tendsto_const_nhds (x := (1 : ℝ))).sub hθlim
  obtain ⟨hInv, hScalar⟩ := tendsto_chartInvGramMatrix_and_scalar_at_zero
    Phi co (by rfl : (Y).D.carrier = Iic 0) (by intro t ht; exact ht)
      x (mem_chart_source H x) (by norm_num : (-1 : ℝ) < 0)
      (fun n => 1 - θ n) ht htend
  have hf₁ : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => ell (y, 1)) x := by
    rw [mdifferentiableAt_iff_source_of_mem_source (mem_chart_source H x),
      I.range_eq_univ, mdifferentiableWithinAt_univ,
      mdifferentiableAt_iff_differentiableAt]
    exact hdiff z hzmid
  have hGrad := tendsto_normGradSqFun_of_chart
    (fun n => co.gInf (1 - θ n)) (co.gInf 0)
    (fun n y => ell (y, θ n)) (fun y => ell (y, 1)) x
    (mem_chart_source H x)
    (Eventually.of_forall fun n => (hsmooth n).mdifferentiableAt (by simp)) hf₁ hInv
    (fun i => ((continuous_id.clm_apply (continuous_const :
      Continuous (fun _ : E →L[ℝ] ℝ => chartModelBasis E i))).tendsto _).comp
        (hD.tendsto_at hzsmall))
  have hLL := locallyLipschitzOn_poleEndpoint_redLength_limit_chart
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ le_rfl hbase
      rho hrho ell hconvJ x hWt hWJ
  have hpath : Tendsto (fun n => (z, θ n)) atTop
      (𝓝[Metric.closedBall z rOut ×ˢ Icc (1 : ℝ) 2] (z, 1)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_const_nhds.prodMk_nhds hθlim,
      Eventually.of_forall fun n => ⟨hzclosed, hθband n⟩⟩
  have hval : Tendsto (fun n => ell (x, θ n)) atTop (𝓝 (ell (x, 1))) := by
    have hv := (hLL.continuousOn (z, 1) ⟨hzclosed, by norm_num⟩).tendsto.comp hpath
    simpa only [Function.comp_def, z, extChartAt_to_inv] using hv
  have hσ : Tendsto (fun n => 1 / θ n) atTop (𝓝 (1 : ℝ)) := by
    simpa only [Pi.div_def, one_div_one] using
      (tendsto_const_nhds (x := (1 : ℝ))).div hθlim (by norm_num : (1 : ℝ) ≠ 0)
  have hleft := hScalar.add hGrad
  have hright : Tendsto (fun n => (1 / θ n) * ell (x, θ n)) atTop
      (𝓝 (ell (x, 1))) := by simpa only [one_mul] using hσ.mul hval
  apply tendsto_nhds_unique_of_eventuallyEq hleft hright
  exact Eventually.of_forall fun n => hnormal n x

end PoleEndpoint

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
