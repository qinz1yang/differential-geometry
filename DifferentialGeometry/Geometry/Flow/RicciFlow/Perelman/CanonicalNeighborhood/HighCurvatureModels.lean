import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureBlowup
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureAncientKappaLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureAncientLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureMixedConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalOrientation

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions (SphereAntipodalQuotient)
open scoped _root_.DifferentialGeometry.Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval}

theorem maximal_point_singularity_model [CompactSpace M] [ConnectedSpace M]
    [T2Space (TangentBundle I3 M)] {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (o : TangentOrientationSection M) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∀ theta : ℝ, 0 < theta →
      ∀ (x : ℕ → M) (t : ℕ → ℝ), (∀ i, t i ∈ Set.Ico theta T) →
        (∀ i s, s ∈ Set.Icc 0 (t i) → ∀ y, S.scalar s y ≤ S.scalar (t i) (x i)) →
        Filter.Tendsto (fun i => S.scalar (t i) (x i)) Filter.atTop Filter.atTop →
        ∃ L : BlowupLimit S o kappa x t, PointedFlowScalarBounded L.model 1 := by
  apply maximal_point_singularity_model_of_atPastMaximum hT S hS o
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  obtain ⟨kappa, hkappa, hbelow⟩ :=
    spatial_no_local_collapsing (I := I3) hT S hS hdim (rho := 1) one_pos
  obtain ⟨_kappa0, _hkappa0, hlimit⟩ := exists_highCurvatureFlowSequence_noncollapsed_metric_limit hT S hS
  refine ⟨kappa, hkappa, ?_⟩
  intro theta htheta x t htpos htmem hpos htlower hscalar hmax
  have hlower : ∀ᶠ i in atTop, theta ≤ t i := Eventually.of_forall htlower
  obtain ⟨P, hcanonical, hconn, hcompact, hsourceconn, _hnested, _hbase, _hscalar, _hsec, _hnon⟩ :=
    hlimit theta htheta x t htmem htpos hpos hmax hlower hscalar
  obtain ⟨N, F, hF, hsource, hmetric, rho, hrho, G, hG0, hGsol, hconv⟩ :=
    exists_highCurvatureFlowSequence_ancient_metric_limit hT S hS x t htmem htpos hpos
      hmax htheta hlower hscalar P hcanonical hcompact
  let L : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval := {
    M := P.limit.M
    basepoint := P.limit.basepoint
    S := { base.metric := G }
    isSolution := hGsol }
  have hmodel : IsAncientKappaSolution kappa L ∧ PointedFlowScalarAtBase L 1 ∧
      PointedFlowScalarBounded L 1 :=
    highCurvatureFlowSequence_ancient_kappa_limit hT S hS x t htmem htpos hpos
      hmax htheta hlower hscalar P hcanonical hconn hkappa hbelow N
      (fun n i => (F n i).base.metric) hsource hmetric rho hrho G hG0 hGsol hconv
  have hpointed := highCurvatureFlowSequence_ancient_limit_pointed_convergence
    hT S hS x t htmem htpos hpos P N (fun n i => (F n i).base.metric)
    hsource hmetric rho hrho G hconv
  have hmixed := highCurvatureFlowSequence_ancient_limit_mixed_convergence
    hT S hS x t htmem htpos hpos P N F hF hsource hmetric rho hrho G hGsol hconv
  obtain ⟨Psi, hPsi, C, hC⟩ := hpointed 0 le_rfl
  have hPsiconn : ∀ i, IsPreconnected (Psi.partialDiffeomorph i).source := by
    intro i
    rw [hPsi]
    exact (hsourceconn (rho i)).isPreconnected
  obtain ⟨sigma, hsigma, O, hO⟩ :=
    exists_subsequence_preserves_tangentOrientation Psi hPsiconn (fun _ => o)
  have hcap : MetricSourceCapture Psi := metricSourceCapture_of_metricConvergenceData C
    (fun k => by rw [hC]; rfl)
    (hmodel.1.complete 0 (by rw [hmodel.1.carrier_eq]; exact (le_rfl : (0 : ℝ) ≤ 0)))
  refine ⟨L, (P.subseq ∘ rho) ∘ sigma, Psi.compSubseq sigma hsigma,
    (P.strictMono.comp hrho).comp hsigma, hmodel.1, hmodel.2.1, ?_, ?_, ?_, O, hO⟩
  · intro s hs
    obtain ⟨Ps, _hPs, Cs, hCs⟩ := hpointed s hs
    refine ⟨Ps.compSubseq sigma hsigma, fun K hK => ?_⟩
    have hc := (Cs.compSubseq sigma hsigma).converges K hK 2
    have hcan : (Cs.compSubseq sigma hsigma).domain =
        CanonicalMetricCompactness.canonicalSourceData (Ps.compSubseq sigma hsigma) := by
      funext i
      change MetricSourceData.compSubseq sigma hsigma i (Cs.domain (sigma i)) = _
      rw [hCs]
      rfl
    rwa [hcan] at hc
  · intro K hK A hA order eta heta
    filter_upwards [hsigma.tendsto_atTop.eventually (hmixed K hK A hA order eta heta)] with i hi
    change K ⊆ (Psi.partialDiffeomorph (sigma i)).source ∧
      Nonempty (MetricComparisonOn G
        (((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).term
          (P.subseq (rho (sigma i)))).S.base.metric)
        (Psi.partialDiffeomorph (sigma i)) K (Icc (-A) 0) order eta)
    rw [hPsi]
    exact hi
  · intro r hr
    exact hsigma.tendsto_atTop.eventually (hcap r hr)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
