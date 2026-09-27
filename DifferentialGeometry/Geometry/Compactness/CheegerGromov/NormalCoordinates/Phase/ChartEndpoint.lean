import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Phase.Endpoint
import DifferentialGeometry.Geometry.Exponential.NormalCoordinates.Convergence

set_option autoImplicit false
noncomputable section
open Bundle Set Manifold
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.CheegerGromovCompactness
open Geometry.Riemannian Geometry.Riemannian.NormalCoordinates Geometry.Riemannian.Exponential

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

omit [T2Space (TangentBundle I M)] in
theorem _root_.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.phase_endpoint_eq_expMapIntrinsic
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {p : M} (c : NormalBallChart (I := I) p)
    {r : ℝ} {R : NNReal} {Z : ℝ → E × E}
    (hrQuarter : Metric.ball (0 : E) r ⊆ Metric.ball (0 : E) (c.radius / 4))
    (hZcont : ContinuousOn Z (Icc (-1) 1))
    (hZwithin : ∀ t ∈ Icc (-1) 1, HasDerivWithinAt Z
      (PhaseFlow.phaseField (c.accel g) (Z t)) (Icc (-1) 1) t)
    (hZmem : ∀ t ∈ Icc (-1) 1, Z t ∈ normalPhaseBox r R) :
    c.hom (Z 1).1 = expMapIntrinsic g hEnorm (c.hom (Z 0).1)
      (mfderiv 𝓘(ℝ, E) I c.hom (Z 0).1 (Z 0).2) := by
  let gamma : ℝ → E := fun t => (Z t).1
  let Gamma : ℝ → M := fun t => c.hom (gamma t)
  have hright : ∀ t ∈ Ico (-1) 1, HasDerivWithinAt Z
      (PhaseFlow.phaseField (c.accel g) (Z t)) (Ici t) t := by
    intro t ht
    exact Analysis.ODE.Flow.hasDerivWithinAt_Ici_of_Icc
      (hZwithin t ⟨ht.1, ht.2.le⟩) ht
  have hZsmooth : ContDiffOn ℝ ∞ Z (Ioo (-1) 1) :=
    chartFlow_contDiff g c (by norm_num) hZcont hright
  have hgamma : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ gamma (Ioo (-1) 1) := by
    rw [contMDiffOn_iff_contDiffOn]
    exact hZsmooth.fst
  have hZat : ∀ t ∈ Ioo (-1) 1, HasDerivAt Z
      (PhaseFlow.phaseField (c.accel g) (Z t)) t := by
    intro t ht
    exact (hZwithin t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hgeo : Geodesic.IsGeodesicOn (I := 𝓘(ℝ, E))
      (c.totalMetric g) gamma (Ioo (-1) 1) := by
    exact chartGeoOn_of_phase g c isOpen_Ioo hZat
  have hmem : ∀ t ∈ Ioo (-1) 1, gamma t ∈ (c.inner : Set E) := by
    intro t ht
    exact hrQuarter (hZmem t (Ioo_subset_Icc_self ht)).1
  have hGammaGeo : Geodesic.IsGeodesicOn g Gamma (Ioo (-1) 1) :=
    c.geo_map g gamma (Ioo (-1) 1) isOpen_Ioo hmem hgamma hgeo
  have hGammaCont : ContinuousOn Gamma (Icc (-1) 1) := by
    apply c.smooth_to.continuousOn.comp hZcont.fst
    intro t ht
    exact c.inner_subset (hrQuarter (hZmem t ht).1)
  have hv : (mfderiv 𝓘(ℝ, ℝ) I Gamma 0 (1 : ℝ) : E) =
      (mfderiv 𝓘(ℝ, E) I c.hom (Z 0).1 (Z 0).2 : E) := by
    have hp : (Z 0).1 ∈ Metric.ball (0 : E) c.radius :=
      c.inner_subset (hrQuarter (hZmem 0 (by norm_num)).1)
    have hgammaDeriv : HasDerivAt gamma (Z 0).2 0 := by
      have hfst := ((hZat 0 (by norm_num)).hasFDerivAt.fst).hasDerivAt
      simpa only [gamma, PhaseFlow.phaseField, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.toSpanSingleton_apply,
        one_smul] using hfst
    have hgammaMd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) gamma 0 := by
      rw [mdifferentiableAt_iff_differentiableAt]
      exact hgammaDeriv.differentiableAt
    have hcMd := ((c.smooth_to (Z 0).1 hp).contMDiffAt
      (Metric.isOpen_ball.mem_nhds hp)).mdifferentiableAt (by simp)
    have hcomp := mfderiv_comp_apply (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, E)) (I'' := I)
      (g := c.hom) (f := gamma) (x := (0 : ℝ)) hcMd hgammaMd (1 : ℝ)
    have hgammaMfd : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) gamma 0 1 = (Z 0).2 := by
      rw [mfderiv_eq_fderiv]
      exact (fderiv_apply_one_eq_deriv (f := gamma) (x := (0 : ℝ))).trans hgammaDeriv.deriv
    change mfderiv 𝓘(ℝ, ℝ) I Gamma 0 1 =
      mfderiv 𝓘(ℝ, E) I c.hom (Z 0).1 (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) gamma 0 1) at hcomp
    exact hcomp.trans (congrArg (fun v : E => mfderiv 𝓘(ℝ, E) I c.hom (Z 0).1 v) hgammaMfd)
  exact geo_end_eq_intr g hEnorm (Gamma 0)
    (mfderiv 𝓘(ℝ, E) I c.hom (Z 0).1 (Z 0).2) hGammaCont hGammaGeo rfl hv

end DifferentialGeometry.CheegerGromovCompactness

end

set_option autoImplicit false
noncomputable section
open Set Manifold
open scoped Manifold ContDiff
namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart
open DifferentialGeometry.CheegerGromovCompactness
variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem isIntegralCurveOn_metricSpray_of_phase
    (g : SmoothRiemannianMetric I M) {p : M} (c : NormalBallChart (I := I) p)
    (b : c.MetricBounds g) {r : ℝ} {R : NNReal} {Z : ℝ → E × E}
    (hrMetric : Metric.ball (0 : E) r ⊆ Metric.ball (0 : E) b.radius)
    (hrQuarter : Metric.ball (0 : E) r ⊆ Metric.ball (0 : E) (c.radius / 4))
    (hZwithin : ∀ t ∈ Icc (-1) 1, HasDerivWithinAt Z
      (PhaseFlow.phaseField (c.accel g) (Z t)) (Icc (-1) 1) t)
    (hZmem : ∀ t ∈ Icc (-1) 1, Z t ∈ normalPhaseBox r R) :
    IsIntegralCurveOn Z (fun _ => MetricKoszul.metricSpray (c.metric g)) (Icc 0 1) := by
  have hsmall : Icc (0 : ℝ) 1 ⊆ Icc (-1) 1 := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  intro t ht
  have hder := (hZwithin t (hsmall ht)).mono hsmall
  have hpos := (hZmem t (hsmall ht)).1
  have hco : IsCoercive (c.metric g (Z t).1) := b.equiv.coercive g (hrMetric hpos)
  have hfield : PhaseFlow.phaseField (c.accel g) (Z t) =
      MetricKoszul.metricSpray (c.metric g) (Z t) := by
    rw [MetricKoszul.metricSpray_eq _ _ hco]
    apply Prod.ext
    · rfl
    · exact c.accel_eq g (Z t) (hrQuarter hpos) hco
  rwa [hfield] at hder

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart

end
