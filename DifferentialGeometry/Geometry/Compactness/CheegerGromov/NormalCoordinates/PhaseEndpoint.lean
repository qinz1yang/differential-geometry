import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.MetricBounds
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.ChartFamily
import DifferentialGeometry.Geometry.Exponential.ExpVariationSmooth


import DifferentialGeometry.Geometry.Exponential.IntrinsicExp
import DifferentialGeometry.Geometry.Exponential.DiagExpDerivative
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import DifferentialGeometry.Geometry.Exponential.NormalBallGeodesic
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.LocalMetric
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.PhaseEndpointInverse
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.PhaseFlowRealization
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.SymmetricPhaseFlow
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.EMetric
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Filter Set Bundle Manifold
open scoped Manifold ContDiff ENNReal NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

private theorem exists_smooth_q
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBounds (I := I) X) {r : Real} (hr : 0 < r) :
    ∃ q : NNReal, 0 < q ∧
      6 * (q : Real) < r ∧
      3 * h.metricC 1 * (2 * (q : Real)) ^ 2 ≤
        (2 / 3 : Real) * (q : Real) ∧
      PhaseFlow.phaseErr (normalPhaseK h (2 * q)) <
        ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
          (E × E) →L[Real] (E × E))‖₊⁻¹ := by
  let : Nontrivial E := Module.nontrivial_of_finrank_pos
    (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank Real E)))
  let threshold : NNReal :=
    ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
      (E × E) →L[Real] (E × E))‖₊⁻¹
  have hthreshold : 0 < threshold := PhaseFlow.freeDiagInv_pos (E := E)
  have htwo : Tendsto (fun q : NNReal ↦ 2 * q) (nhds 0) (nhds 0) := by
    have hcont : Continuous (fun q : NNReal ↦ 2 * q) :=
      continuous_const.mul continuous_id
    have hAt : Tendsto (fun q : NNReal ↦ 2 * q) (nhds (0 : NNReal))
        (nhds ((fun q : NNReal ↦ 2 * q) 0)) := hcont.continuousAt
    simpa using hAt
  have herrEv : ∀ᶠ q : NNReal in nhds 0,
      PhaseFlow.phaseErr (normalPhaseK h (2 * q)) < threshold :=
    htwo (normalPhaseErr_lt_ev (I := I) h hthreshold)
  obtain ⟨eps, heps, herr⟩ := Metric.eventually_nhds_iff_ball.mp herrEv
  let C : Real := h.metricC 1
  have hC : 0 ≤ C := h.metricC_nonneg 1
  let accelBound : Real := 1 / (18 * (C + 1))
  have hden : 0 < 18 * (C + 1) := mul_pos (by norm_num) (by linarith)
  have haccelBound : 0 < accelBound := one_div_pos.mpr hden
  let qReal : Real := min (eps / 4) (min (r / 12) accelBound)
  have hqReal : 0 < qReal := by
    dsimp only [qReal]
    exact lt_min (div_pos heps (by norm_num))
      (lt_min (div_pos hr (by norm_num)) haccelBound)
  let q : NNReal := ⟨qReal, hqReal.le⟩
  have hqEps : qReal ≤ eps / 4 := min_le_left _ _
  have hqRadius : qReal ≤ r / 12 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hqAccel : qReal ≤ accelBound :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hqBall : q ∈ Metric.ball (0 : NNReal) eps := by
    rw [Metric.mem_ball, NNReal.dist_eq]
    change |qReal - 0| < eps
    rw [sub_zero, abs_of_pos hqReal]
    exact hqEps.trans_lt (div_lt_self heps (by norm_num))
  have herrQ : PhaseFlow.phaseErr (normalPhaseK h (2 * q)) < threshold :=
    herr q hqBall
  have hqRadius' : 6 * qReal < r := by
    nlinarith
  have hqProd : qReal * (18 * (C + 1)) ≤ 1 := by
    apply (le_div_iff₀ hden).mp
    simpa only [accelBound, one_div] using hqAccel
  have hlinear : 18 * C * qReal ≤ 1 := by
    nlinarith
  have hcoef : 12 * C * qReal ≤ (2 / 3 : Real) := by
    nlinarith
  have hmul : 0 ≤ qReal * ((2 / 3 : Real) - 12 * C * qReal) :=
    mul_nonneg hqReal.le (sub_nonneg.mpr hcoef)
  refine ⟨q, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast hqReal
  · change 6 * qReal < r
    exact hqRadius'
  · change 3 * C * (2 * qReal) ^ 2 ≤ (2 / 3 : Real) * qReal
    nlinarith
  · simpa only [threshold] using herrQ

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem normal_enorm
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
      Y.riemBundle (I := I)
    IsMetricNorm (I := I) (M := Y.M) Y.metric := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
    Y.riemBundle (I := I)
  let : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  intro y v
  exact tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) Y.metric y v

noncomputable def normalTangent
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (z : E × E)
    (c : NormalChartAt (I := I) Y x := c2RadiusNormalBallChart (I := I) Y x) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    TangentBundle I Y.M := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  exact c.tangent z

noncomputable def normalPair
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (z : E × E)
    (c : NormalChartAt (I := I) Y x := c2RadiusNormalBallChart (I := I) Y x) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    Y.M × Y.M := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  exact c.pair z

def IsNormalDiag
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) (q : NNReal) (δ : Real)
    (e : OpenPartialHomeomorph (E × E) (E × E))
    (c : NormalChartAt (I := I) Y x := c2RadiusNormalBallChart (I := I) Y x) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : ConnectedSpace Y.M := hconn
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace Y.M :=
      Manifold.metrizableSpace I Y.M
    letI : T3Space Y.M := inferInstance
    letI : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
      Y.riemBundle (I := I)
    letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun y : Y.M ↦ TangentSpace I y) := Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
    Prop := by
  let _ := hconn
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space Y.M := Y.t2
  letI : ConnectedSpace Y.M := hconn
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  letI : T3Space Y.M := inferInstance
  letI : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
    Y.riemBundle (I := I)
  letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun y : Y.M ↦ TangentSpace I y) := Y.riemBundle_cont (I := I)
  letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
  letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  exact
    e.source = Metric.ball (0 : E × E) q ∧
    e 0 = 0 ∧
    ContDiffOn Real ∞ (e : E × E → E × E) e.source ∧
    Metric.closedBall (0 : E × E) δ ⊆ e.target ∧
    ContDiffOn Real ∞ e.symm e.target ∧
    ∀ z ∈ Metric.closedBall (0 : E × E) q,
      normalPair (I := I) Y x (e z) (c := c) =
        diagExp (I := I) Y.metric (normal_enorm (I := I) Y)
          (normalTangent (I := I) Y x z (c := c))

def NormalDiagFence
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (q : NNReal) (e : OpenPartialHomeomorph (E × E) (E × E))
    (c : NormalChartAt (I := I) Y x := c2RadiusNormalBallChart (I := I) Y x) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    Prop := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  exact ∀ z ∈ Metric.closedBall (0 : E × E) q,
    z.1 ∈ Metric.ball (0 : E) c.radius ∧
    (e z).1 ∈ Metric.ball (0 : E) c.radius ∧
    (e z).2 ∈ Metric.ball (0 : E) c.radius

omit [NeZero (Module.finrank ℝ E)] in
theorem normal_launch_mfd
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    {Z : Real → E × E}
    (hZat : HasDerivAt Z
      (PhaseFlow.phaseField (normalAccel (I := I) Y x) (Z 0)) 0)
    (hpos :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      (Z 0).1 ∈ Metric.ball (0 : E)
        (expMapC2Radius (I := I) Y.metric x)) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    mfderiv 𝓘(Real, Real) I
        (fun t : Real ↦ expMapDiffeo (I := I) Y.metric x (Z t).1) 0 1 =
      mfderiv 𝓘(Real, E) I
        (fun u : E ↦ expMapDiffeo (I := I) Y.metric x u) (Z 0).1 (Z 0).2 := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let gamma : Real → E := fun t ↦ (Z t).1
  have hgammaDeriv : HasDerivAt gamma (Z 0).2 0 := by
    have hfst := (hZat.hasFDerivAt.fst).hasDerivAt
    simpa only [gamma, PhaseFlow.phaseField, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.toSpanSingleton_apply,
      one_smul] using hfst
  have hgammaMd : MDifferentiableAt 𝓘(Real, Real) 𝓘(Real, E) gamma 0 := by
    rw [mdifferentiableAt_iff_differentiableAt]
    exact hgammaDeriv.differentiableAt
  have hExpMd : MDifferentiableAt 𝓘(Real, E) I
      (fun u : E ↦ expMapDiffeo (I := I) Y.metric x u) (Z 0).1 :=
    (((exp_map_diffeo_cont_mdiff_on_exp_ball (I := I) Y x) (Z 0).1 hpos).contMDiffAt
      (Metric.isOpen_ball.mem_nhds hpos)).mdifferentiableAt (by simp)
  have hgammaMfd : mfderiv 𝓘(Real, Real) 𝓘(Real, E) gamma 0 1 = (Z 0).2 := by
    rw [mfderiv_eq_fderiv]
    exact (fderiv_apply_one_eq_deriv (f := gamma) (x := (0 : Real))).trans
      hgammaDeriv.deriv
  have hcomp := mfderiv_comp_apply
    (I := 𝓘(Real, Real)) (I' := 𝓘(Real, E)) (I'' := I)
    (g := fun u : E ↦ expMapDiffeo (I := I) Y.metric x u)
    (f := gamma) (x := (0 : Real)) hExpMd hgammaMd (1 : Real)
  change mfderiv 𝓘(Real, Real) I
      (fun t : Real ↦ expMapDiffeo (I := I) Y.metric x (Z t).1) 0 1 =
    mfderiv 𝓘(Real, E) I
      (fun u : E ↦ expMapDiffeo (I := I) Y.metric x u) (gamma 0)
        (mfderiv 𝓘(Real, Real) 𝓘(Real, E) gamma 0 1) at hcomp
  calc
    mfderiv 𝓘(Real, Real) I
        (fun t : Real ↦ expMapDiffeo (I := I) Y.metric x (Z t).1) 0 1 =
      mfderiv 𝓘(Real, E) I
        (fun u : E ↦ expMapDiffeo (I := I) Y.metric x u) (gamma 0)
          (mfderiv 𝓘(Real, Real) 𝓘(Real, E) gamma 0 1) := by
      simpa only [gamma, Function.comp_apply] using hcomp
    _ = mfderiv 𝓘(Real, E) I
        (fun u : E ↦ expMapDiffeo (I := I) Y.metric x u) (Z 0).1 (Z 0).2 := by
      rw [hgammaMfd]

theorem normal_end_eq_intr
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M)
    {r : Real} {R : NNReal} {Z : Real → E × E}
    (hrQuarter :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      Metric.ball (0 : E) r ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) Y.metric x / 4))
    (hZcont : ContinuousOn Z (Icc (-1) 1))
    (hZwithin : ∀ t ∈ Icc (-1) 1, HasDerivWithinAt Z
      (PhaseFlow.phaseField (normalAccel (I := I) Y x) (Z t))
      (Icc (-1) 1) t)
    (hZmem : ∀ t ∈ Icc (-1) 1, Z t ∈ normalPhaseBox r R) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : ConnectedSpace Y.M := hconn
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace Y.M :=
      Manifold.metrizableSpace I Y.M
    letI : T3Space Y.M := inferInstance
    letI : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
      Y.riemBundle (I := I)
    letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun y : Y.M ↦ TangentSpace I y) := Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
    expMapDiffeo (I := I) Y.metric x (Z 1).1 =
      expMapIntrinsic (I := I) Y.metric (normal_enorm (I := I) Y)
        (expMapDiffeo (I := I) Y.metric x (Z 0).1)
        (mfderiv 𝓘(Real, Real) I
          (fun t : Real ↦ expMapDiffeo (I := I) Y.metric x (Z t).1) 0 1) := by
  let _ := hconn
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : ConnectedSpace Y.M := hconn
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Y.M := Manifold.metrizableSpace I Y.M
  let : T3Space Y.M := inferInstance
  let : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
    Y.riemBundle (I := I)
  let : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : Y.M ↦ TangentSpace I y) := Y.riemBundle_cont (I := I)
  let : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  let gamma : Real → E := fun t ↦ (Z t).1
  let Gamma : Real → Y.M :=
    fun t ↦ expMapDiffeo (I := I) Y.metric x (gamma t)
  have hright : ∀ t ∈ Ico (-1) 1, HasDerivWithinAt Z
      (PhaseFlow.phaseField (normalAccel (I := I) Y x) (Z t)) (Ici t) t := by
    intro t ht
    exact Analysis.ODE.Flow.hasDerivWithinAt_Ici_of_Icc
      (hZwithin t ⟨ht.1, ht.2.le⟩) ht
  have hZsmooth : ContDiffOn Real ∞ Z (Ioo (-1) 1) :=
    normalFlow_contDiff (I := I) Y x (by norm_num) hZcont hright
  have hgamma : ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) ∞ gamma (Ioo (-1) 1) := by
    rw [contMDiffOn_iff_contDiffOn]
    exact hZsmooth.fst
  have hZat : ∀ t ∈ Ioo (-1) 1, HasDerivAt Z
      (PhaseFlow.phaseField (normalAccel (I := I) Y x) (Z t)) t := by
    intro t ht
    exact (hZwithin t (Ioo_subset_Icc_self ht)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)
  have hgeo : Geodesic.IsGeodesicOn (I := 𝓘(Real, E))
      (normalTotal (I := I) Y x) gamma (Ioo (-1) 1) := by
    simpa only [gamma] using
      normalGeoOn_of_phase (I := I) Y x isOpen_Ioo hZat
  have hmem : ∀ t ∈ Ioo (-1) 1,
      gamma t ∈ (normalQuarter (I := I) Y x : Set E) := by
    intro t ht
    exact hrQuarter (hZmem t (Ioo_subset_Icc_self ht)).1
  have hGammaGeo : Geodesic.IsGeodesicOn (I := I) Y.metric Gamma (Ioo (-1) 1) := by
    simpa only [Gamma, gamma] using
      normalGeo_map (I := I) Y x gamma (Ioo (-1) 1) isOpen_Ioo
        hmem hgamma hgeo
  have hGammaCont : ContinuousOn Gamma (Icc (-1) 1) := by
    have hExp :=
      (exp_map_diffeo_cont_mdiff_on_exp_ball (I := I) Y x).continuousOn
    apply hExp.comp hZcont.fst
    intro t ht
    have hquarter := hrQuarter (hZmem t ht).1
    exact (Metric.ball_subset_ball (by
      nlinarith [expMapC2Radius_pos (I := I) Y.metric x])) hquarter
  simpa only [Gamma, gamma] using
    (geo_end_eq_intr (I := I) Y.metric (normal_enorm (I := I) Y)
      (Gamma 0)
      (mfderiv 𝓘(Real, Real) I Gamma 0 1)
      hGammaCont hGammaGeo rfl rfl)

theorem normal_end_eq_diag
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) {r : Real} {R : NNReal} {Z : Real → E × E}
    (hrQuarter :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      Metric.ball (0 : E) r ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) Y.metric x / 4))
    (hZcont : ContinuousOn Z (Icc (-1) 1))
    (hZwithin : ∀ t ∈ Icc (-1) 1, HasDerivWithinAt Z
      (PhaseFlow.phaseField (normalAccel (I := I) Y x) (Z t))
      (Icc (-1) 1) t)
    (hZmem : ∀ t ∈ Icc (-1) 1, Z t ∈ normalPhaseBox r R) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : ConnectedSpace Y.M := hconn
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace Y.M :=
      Manifold.metrizableSpace I Y.M
    letI : T3Space Y.M := inferInstance
    letI : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
      Y.riemBundle (I := I)
    letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun y : Y.M ↦ TangentSpace I y) := Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
    normalPair (I := I) Y x ((Z 0).1, (Z 1).1) =
      diagExp (I := I) Y.metric (normal_enorm (I := I) Y)
        (normalTangent (I := I) Y x (Z 0)) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : ConnectedSpace Y.M := hconn
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Y.M := Manifold.metrizableSpace I Y.M
  let : T3Space Y.M := inferInstance
  let : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
    Y.riemBundle (I := I)
  let : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : Y.M ↦ TangentSpace I y) := Y.riemBundle_cont (I := I)
  let : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  have h0 : (0 : Real) ∈ Icc (-1) 1 := by norm_num
  have hZat : HasDerivAt Z
      (PhaseFlow.phaseField (normalAccel (I := I) Y x) (Z 0)) 0 :=
    (hZwithin 0 h0).hasDerivAt (Icc_mem_nhds (by norm_num) (by norm_num))
  have hpos : (Z 0).1 ∈ Metric.ball (0 : E)
      (expMapC2Radius (I := I) Y.metric x) := by
    have hquarter := hrQuarter (hZmem 0 h0).1
    exact (Metric.ball_subset_ball (by
      nlinarith [expMapC2Radius_pos (I := I) Y.metric x])) hquarter
  have hlaunch := normal_launch_mfd (I := I) Y x hZat hpos
  have hend := normal_end_eq_intr (I := I) Y hcomplete hconn x
    hrQuarter hZcont hZwithin hZmem
  rw [hlaunch] at hend
  rw [normalPair, normalTangent, diagExp_apply]
  exact Prod.ext rfl hend

theorem exists_normal_diag
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBounds (I := I) X)
    (k : Nat) (x : (X.obj k).M) {r : Real} (hr : 0 < r)
    (hcomplete : MetricComplete (I := I) (X.obj k))
    (hconn :
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (hrMetric : Metric.ball (0 : E) r ⊆
      Metric.ball (0 : E) (h.radius k x))
    (hrQuarter :
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) :=
        (X.obj k).t2TangentBundle
      Metric.ball (0 : E) r ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj k).metric x / 4)) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : IsManifold I 1 (X.obj k).M := IsManifold.of_le
      (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
    letI : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
    letI : T2Space (X.obj k).M := (X.obj k).t2
    letI : ConnectedSpace (X.obj k).M := hconn
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace (X.obj k).M :=
      Manifold.metrizableSpace I (X.obj k).M
    letI : T3Space (X.obj k).M := inferInstance
    letI : RiemannianBundle
        (fun y : (X.obj k).M ↦ TangentSpace I y) :=
      (X.obj k).riemBundle (I := I)
    letI : (y : (X.obj k).M) → InnerProductSpace Real (TangentSpace I y) :=
      (X.obj k).riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun y : (X.obj k).M ↦ TangentSpace I y) :=
      (X.obj k).riemBundle_cont (I := I)
    letI : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
    letI : CompleteSpace (X.obj k).M :=
      MetricComplete.complete (I := I) (X.obj k) hcomplete
    ∃ (q : NNReal) (Φ : (E × E) → Real → E × E)
        (e : OpenPartialHomeomorph (E × E) (E × E)) (δ : Real),
      0 < q ∧
      4 * (q : Real) < r ∧
      (∀ z ∈ Metric.closedBall (0 : E × E) q, Φ z 0 = z) ∧
      (∀ z ∈ Metric.closedBall (0 : E × E) q,
        ContinuousOn (Φ z) (Icc (-1) 1)) ∧
      (∀ z ∈ Metric.closedBall (0 : E × E) q, ∀ t ∈ Icc (-1) 1,
        HasDerivWithinAt (Φ z)
          (PhaseFlow.phaseField (normalAccel (I := I) (X.obj k) x) (Φ z t))
          (Icc (-1) 1) t) ∧
      (∀ z ∈ Metric.closedBall (0 : E × E) q, ∀ t ∈ Ioo (-1) 1,
        HasDerivAt (Φ z)
          (PhaseFlow.phaseField (normalAccel (I := I) (X.obj k) x) (Φ z t)) t) ∧
      (∀ z ∈ Metric.closedBall (0 : E × E) q, ∀ t ∈ Icc (-1) 1,
        Φ z t ∈ normalPhaseBox r (2 * q)) ∧
      ApproximatesLinearOn (fun z ↦ (z.1, (Φ z 1).1)) PhaseFlow.freeDiag
        (Metric.closedBall (0 : E × E) q)
        (PhaseFlow.phaseErr (normalPhaseK h (2 * q))) ∧
      ContDiffOn Real ∞ (fun z ↦ (z.1, (Φ z 1).1))
        (Metric.ball (0 : E × E) q) ∧
      0 < δ ∧
      e.source = Metric.ball (0 : E × E) q ∧
      (e : E × E → E × E) = (fun z ↦ (z.1, (Φ z 1).1)) ∧
      Metric.closedBall ((fun z ↦ (z.1, (Φ z 1).1)) 0) δ ⊆ e.target ∧
      δ = ((‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊⁻¹ -
          PhaseFlow.phaseErr (normalPhaseK h (2 * q)) : NNReal) : Real) *
        ((q : Real) / 2) ∧
      ContDiffOn Real ∞ e.symm e.target ∧
      ∀ z ∈ Metric.closedBall (0 : E × E) q,
        normalPair (I := I) (X.obj k) x (e z) =
          diagExp (I := I) (X.obj k).metric
            (normal_enorm (I := I) (X.obj k))
            (normalTangent (I := I) (X.obj k) x z) := by
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : IsManifold I 1 (X.obj k).M := IsManifold.of_le
    (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
  let : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  let : T2Space (X.obj k).M := (X.obj k).t2
  let : ConnectedSpace (X.obj k).M := hconn
  let : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  let : TopologicalSpace.MetrizableSpace (X.obj k).M :=
    Manifold.metrizableSpace I (X.obj k).M
  let : T3Space (X.obj k).M := inferInstance
  let : RiemannianBundle (fun y : (X.obj k).M ↦ TangentSpace I y) :=
    (X.obj k).riemBundle (I := I)
  let : (y : (X.obj k).M) → InnerProductSpace Real (TangentSpace I y) :=
    (X.obj k).riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : (X.obj k).M ↦ TangentSpace I y) :=
    (X.obj k).riemBundle_cont (I := I)
  let : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
  let : CompleteSpace (X.obj k).M :=
    MetricComplete.complete (I := I) (X.obj k) hcomplete
  obtain ⟨q, hq, hqWide, hqAccel, herr⟩ :=
    exists_smooth_q (I := I) h hr
  have hqRadius : 4 * (q : Real) < r := by nlinarith [hqWide]
  obtain ⟨Φ, hΦ0, hΦcont, hΦwithin, hΦat, hΦbox, _hΦzero,
      happrox, hΦsmooth⟩ :=
    exists_normal_biflow (I := I) h k x hrMetric hrQuarter q hq
      hqWide hqAccel
  obtain ⟨e, δ, hδ, hsource, hcoe, htarget, hδeq⟩ :=
    PhaseFlow.exists_quant_inv hq happrox herr
  have happroxOpen : ApproximatesLinearOn
      (fun z ↦ (z.1, (Φ z 1).1))
      (PhaseFlow.freeDiagCLE (E := E) : (E × E) →L[Real] (E × E))
      (Metric.ball (0 : E × E) q)
      (PhaseFlow.phaseErr (normalPhaseK h (2 * q))) := by
    simpa only [PhaseFlow.freeDiagCLE_coe] using
      happrox.mono_set Metric.ball_subset_closedBall
  have hinvSmooth : ContDiffOn Real ∞ e.symm e.target :=
    PhaseFlow.inv_smooth_of_approx happroxOpen (Or.inr herr)
      Metric.isOpen_ball hΦsmooth e hsource hcoe
  refine ⟨q, Φ, e, δ, hq, hqRadius, hΦ0, hΦcont, hΦwithin, hΦat,
    hΦbox, happrox, hΦsmooth, hδ, hsource, hcoe, htarget, hδeq, hinvSmooth, ?_⟩
  intro z hz
  have hdiag := normal_end_eq_diag (I := I) (X.obj k) hcomplete hconn x
    hrQuarter (hΦcont z hz) (hΦwithin z hz) (hΦbox z hz)
  rw [hcoe]
  simpa only [hΦ0 z hz] using hdiag

namespace NormalRadiusProfile

theorem exists_flow_at
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBounds (I := I) X}
    (h : NormalRadiusProfile hd hb)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (R : Real) (q : NNReal) (hq : 0 < q)
    (hqWide : 6 * (q : Real) < h.phaseRadius R)
    (hqAccel : 3 * hb.metricC 1 * (2 * (q : Real)) ^ 2 ≤
      (2 / 3 : Real) * (q : Real))
    (herr : PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) <
      ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊⁻¹) :
    ∃ δ : Real,
      0 < δ ∧
      δ = ((‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊⁻¹ -
          PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) : NNReal) : Real) *
        ((q : Real) / 2) ∧
      ∀ k (x : (X.obj k).M),
        hd.dist k x (X.obj k).basepoint ≤ R →
        ∃ (Φ : (E × E) → Real → E × E)
            (e : OpenPartialHomeomorph (E × E) (E × E)),
          (∀ z ∈ Metric.closedBall (0 : E × E) q, Φ z 0 = z) ∧
          (∀ z ∈ Metric.closedBall (0 : E × E) q,
            IsIntegralCurveOn (Φ z)
              (fun _ ↦ MetricKoszul.metricSpray
                (normalCoordMetric (I := I) (X.obj k) x))
              (Icc 0 1)) ∧
          (∀ z ∈ Metric.closedBall (0 : E × E) q,
            ∀ t ∈ Icc (0 : Real) 1,
              (Φ z t).1 ∈ Metric.ball (0 : E) (h.phaseRadius R)) ∧
          (e : E × E → E × E) = (fun z ↦ (z.1, (Φ z 1).1)) ∧
          IsNormalDiag (I := I) (X.obj k) (hcomplete.complete k) (hconn k)
            x q δ e ∧
          NormalDiagFence (I := I) (X.obj k) x q e := by
  let δ : Real := ((‖((PhaseFlow.freeDiagCLE (E := E)).symm :
      (E × E) →L[Real] (E × E))‖₊⁻¹ -
        PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) : NNReal) : Real) *
    ((q : Real) / 2)
  have hmargin : 0 <
      ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊⁻¹ -
          PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) :=
    tsub_pos_iff_lt.mpr herr
  have hqReal : (0 : Real) < q := by exact_mod_cast hq
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact mul_pos (by exact_mod_cast hmargin) (div_pos hqReal (by norm_num))
  refine ⟨δ, hδ, rfl, ?_⟩
  intro k x hx
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : IsManifold I 1 (X.obj k).M := IsManifold.of_le
    (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
  let : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
  let : T2Space (X.obj k).M := (X.obj k).t2
  let : ConnectedSpace (X.obj k).M := hconn k
  let : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  let : TopologicalSpace.MetrizableSpace (X.obj k).M :=
    Manifold.metrizableSpace I (X.obj k).M
  let : T3Space (X.obj k).M := inferInstance
  let : RiemannianBundle
      (fun y : (X.obj k).M ↦ TangentSpace I y) :=
    (X.obj k).riemBundle (I := I)
  let : (y : (X.obj k).M) → InnerProductSpace Real (TangentSpace I y) :=
    (X.obj k).riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : (X.obj k).M ↦ TangentSpace I y) :=
    (X.obj k).riemBundle_cont (I := I)
  let : EMetricSpace (X.obj k).M := (X.obj k).emetricSpace (I := I)
  let : CompleteSpace (X.obj k).M :=
    MetricComplete.complete (I := I) (X.obj k) (hcomplete.complete k)
  have hrMetric := h.phaseRadius_metric hx
  have hrQuarter := h.phaseRadius_exp hx
  obtain ⟨Φ, hΦ0, hΦcont, hΦwithin, _hΦat, hΦbox, hΦzero,
      happrox, hΦsmooth⟩ :=
    exists_normal_biflow (I := I) hb k x hrMetric hrQuarter q hq
      hqWide hqAccel
  obtain ⟨e, δ', _hδ', hsource, hcoe, htarget, hδeq⟩ :=
    PhaseFlow.exists_quant_inv hq happrox herr
  have hδ'eq : δ' = δ := by
    simpa only [δ] using hδeq
  have heSmooth : ContDiffOn Real ∞ (e : E × E → E × E) e.source := by
    rw [hsource, hcoe]
    exact hΦsmooth
  have heZero : e 0 = 0 := by
    rw [hcoe]
    simp only [Prod.fst_zero, hΦzero]
    rfl
  have htargetE : Metric.closedBall (e 0) δ' ⊆ e.target := by
    simpa only [hcoe] using htarget
  have htarget' : Metric.closedBall (0 : E × E) δ ⊆ e.target := by
    simpa only [heZero, hδ'eq] using htargetE
  have happroxOpen : ApproximatesLinearOn
      (fun z ↦ (z.1, (Φ z 1).1))
      (PhaseFlow.freeDiagCLE (E := E) : (E × E) →L[Real] (E × E))
      (Metric.ball (0 : E × E) q)
      (PhaseFlow.phaseErr (normalPhaseK hb (2 * q))) := by
    simpa only [PhaseFlow.freeDiagCLE_coe] using
      happrox.mono_set Metric.ball_subset_closedBall
  have hinvSmooth : ContDiffOn Real ∞ e.symm e.target :=
    PhaseFlow.inv_smooth_of_approx happroxOpen (Or.inr herr)
      Metric.isOpen_ball hΦsmooth e hsource hcoe
  have hdiag : ∀ z ∈ Metric.closedBall (0 : E × E) q,
      normalPair (I := I) (X.obj k) x (e z) =
        diagExp (I := I) (X.obj k).metric
          (normal_enorm (I := I) (X.obj k))
          (normalTangent (I := I) (X.obj k) x z) := by
    intro z hz
    have hzdiag := normal_end_eq_diag (I := I) (X.obj k)
      (hcomplete.complete k) (hconn k) x hrQuarter
      (hΦcont z hz) (hΦwithin z hz) (hΦbox z hz)
    rw [hcoe]
    simpa only [hΦ0 z hz] using hzdiag
  have hsmall : Icc (0 : Real) 1 ⊆ Icc (-1) 1 := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  have hstay : ∀ z ∈ Metric.closedBall (0 : E × E) q,
      ∀ t ∈ Icc (0 : Real) 1,
        (Φ z t).1 ∈ Metric.ball (0 : E) (h.phaseRadius R) := by
    intro z hz t ht
    exact (hΦbox z hz t (hsmall ht)).1
  have hcurve : ∀ z ∈ Metric.closedBall (0 : E × E) q,
      IsIntegralCurveOn (Φ z)
        (fun _ ↦ MetricKoszul.metricSpray
          (normalCoordMetric (I := I) (X.obj k) x))
        (Icc 0 1) := by
    intro z hz t ht
    have htWide : t ∈ Icc (-1 : Real) 1 := hsmall ht
    have hpos := hstay z hz t ht
    have hco : IsCoercive
        (normalCoordMetric (I := I) (X.obj k) x (Φ z t).1) :=
      (hb.metric_equiv k x).coercive (hrMetric hpos)
    have hspray := normalPhase_eq_spray (I := I) (X.obj k) x (Φ z t)
      (hrQuarter hpos) hco
    change HasDerivWithinAt (Φ z)
      (MetricKoszul.metricSpray
        (normalCoordMetric (I := I) (X.obj k) x) (Φ z t))
      (Icc 0 1) t
    rw [← hspray]
    exact (hΦwithin z hz t htWide).mono hsmall
  have heDiag : IsNormalDiag (I := I) (X.obj k)
      (hcomplete.complete k) (hconn k) x q δ e := by
    change e.source = Metric.ball (0 : E × E) q ∧
      e 0 = 0 ∧
      ContDiffOn Real ∞ (e : E × E → E × E) e.source ∧
      Metric.closedBall (0 : E × E) δ ⊆ e.target ∧
      ContDiffOn Real ∞ e.symm e.target ∧
      ∀ z ∈ Metric.closedBall (0 : E × E) q,
        normalPair (I := I) (X.obj k) x (e z) =
          diagExp (I := I) (X.obj k).metric
            (normal_enorm (I := I) (X.obj k))
            (normalTangent (I := I) (X.obj k) x z)
    exact ⟨hsource, heZero, heSmooth, htarget', hinvSmooth, hdiag⟩
  have hfence : NormalDiagFence (I := I) (X.obj k) x q e := by
    intro z hz
    have hzNorm : ‖z‖ ≤ (q : Real) := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    have hqr : (q : Real) < h.phaseRadius R := by
      nlinarith [hqWide]
    have hzFirst : z.1 ∈ Metric.ball (0 : E) (h.phaseRadius R) := by
      rw [Metric.mem_ball, dist_zero_right]
      exact (norm_fst_le z).trans_lt (hzNorm.trans_lt hqr)
    have htime : (1 : Real) ∈ Set.Icc (-1) 1 := by norm_num
    have hzEnd : (Φ z 1).1 ∈ Metric.ball (0 : E) (h.phaseRadius R) :=
      (hΦbox z hz 1 htime).1
    have hExpPos := expMapC2Radius_pos (I := I) (X.obj k).metric x
    have hrNormal : Metric.ball (0 : E) (h.phaseRadius R) ⊆
        normalBall (I := I) (X.obj k) x := by
      intro v hv
      have hvQuarter := hrQuarter hv
      change v ∈ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj k).metric x)
      exact Metric.ball_subset_ball (by nlinarith) hvQuarter
    have hzFirst' := hrNormal hzFirst
    have hzEnd' := hrNormal hzEnd
    rw [hcoe]
    exact ⟨hzFirst', hzFirst', hzEnd'⟩
  exact ⟨Φ, e, hΦ0, hcurve, hstay, hcoe, heDiag, hfence⟩

theorem exists_uniform_flow
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBounds (I := I) X}
    (h : NormalRadiusProfile hd hb)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (R : Real) :
    ∃ (q : NNReal) (δ : Real),
      0 < q ∧
      4 * (q : Real) < h.phaseRadius R ∧
      0 < δ ∧
      δ = ((‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊⁻¹ -
          PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) : NNReal) : Real) *
        ((q : Real) / 2) ∧
      ∀ k (x : (X.obj k).M),
        hd.dist k x (X.obj k).basepoint ≤ R →
        ∃ (Φ : (E × E) → Real → E × E)
            (e : OpenPartialHomeomorph (E × E) (E × E)),
          (∀ z ∈ Metric.closedBall (0 : E × E) q, Φ z 0 = z) ∧
          (∀ z ∈ Metric.closedBall (0 : E × E) q,
            IsIntegralCurveOn (Φ z)
              (fun _ ↦ MetricKoszul.metricSpray
                (normalCoordMetric (I := I) (X.obj k) x))
              (Icc 0 1)) ∧
          (∀ z ∈ Metric.closedBall (0 : E × E) q,
            ∀ t ∈ Icc (0 : Real) 1,
              (Φ z t).1 ∈ Metric.ball (0 : E) (h.phaseRadius R)) ∧
          (e : E × E → E × E) = (fun z ↦ (z.1, (Φ z 1).1)) ∧
          IsNormalDiag (I := I) (X.obj k) (hcomplete.complete k) (hconn k)
            x q δ e := by
  obtain ⟨q, hq, hqWide, hqAccel, herr⟩ :=
    exists_smooth_q (I := I) hb (h.phaseRadius_pos R)
  obtain ⟨δ, hδ, hδeq, hflow⟩ :=
    h.exists_flow_at hcomplete hconn R q hq hqWide hqAccel herr
  have hqRadius : 4 * (q : Real) < h.phaseRadius R := by
    nlinarith [hqWide]
  refine ⟨q, δ, hq, hqRadius, hδ, hδeq, ?_⟩
  intro k x hx
  obtain ⟨Φ, e, hΦ0, hΦcurve, hΦstay, he, hdiag, _hfence⟩ := hflow k x hx
  exact ⟨Φ, e, hΦ0, hΦcurve, hΦstay, he, hdiag⟩

theorem exists_uniform_diag
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    {hb : NormalCoordMetricBounds (I := I) X}
    (h : NormalRadiusProfile hd hb)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (R : Real) :
    ∃ (q : NNReal) (δ : Real),
      0 < q ∧
      4 * (q : Real) < h.phaseRadius R ∧
      0 < δ ∧
      δ = ((‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊⁻¹ -
          PhaseFlow.phaseErr (normalPhaseK hb (2 * q)) : NNReal) : Real) *
        ((q : Real) / 2) ∧
      ∀ k (x : (X.obj k).M),
        hd.dist k x (X.obj k).basepoint ≤ R →
        ∃ e : OpenPartialHomeomorph (E × E) (E × E),
          IsNormalDiag (I := I) (X.obj k) (hcomplete.complete k) (hconn k)
            x q δ e := by
  obtain ⟨q, δ, hq, hqR, hδ, hδeq, hflow⟩ :=
    h.exists_uniform_flow hcomplete hconn R
  refine ⟨q, δ, hq, hqR, hδ, hδeq, ?_⟩
  intro k x hx
  obtain ⟨_Φ, e, _h0, _hcurve, _hstay, _hcoe, he⟩ := hflow k x hx
  exact ⟨e, he⟩

end NormalRadiusProfile

theorem normal_inv_eq
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) (y z : E × E) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : ConnectedSpace Y.M := hconn
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace Y.M :=
      Manifold.metrizableSpace I Y.M
    letI : T3Space Y.M := inferInstance
    letI : RiemannianBundle (fun p : Y.M ↦ TangentSpace I p) :=
      Y.riemBundle (I := I)
    letI : (p : Y.M) → InnerProductSpace Real (TangentSpace I p) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun p : Y.M ↦ TangentSpace I p) := Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
    normalPair (I := I) Y x y =
        diagExp (I := I) Y.metric (normal_enorm (I := I) Y)
          (normalTangent (I := I) Y x z) →
    (diagExpInv (I := I) Y.metric (normal_enorm (I := I) Y) x
        (normalPair (I := I) Y x y)).proj =
      (normalPair (I := I) Y x y).1 →
    expMapIntrinsic (I := I) Y.metric (normal_enorm (I := I) Y)
        (normalPair (I := I) Y x y).1
        (diagExpInv (I := I) Y.metric (normal_enorm (I := I) Y) x
          (normalPair (I := I) Y x y)).snd =
      (normalPair (I := I) Y x y).2 →
    Real.sqrt (Y.metric.inner (normalPair (I := I) Y x y).1
        (diagExpInv (I := I) Y.metric (normal_enorm (I := I) Y) x
          (normalPair (I := I) Y x y)).snd
        (diagExpInv (I := I) Y.metric (normal_enorm (I := I) Y) x
          (normalPair (I := I) Y x y)).snd) <
      expDiffeoRadius (I := I) Y.metric (normal_enorm (I := I) Y)
        (normalPair (I := I) Y x y).1 →
    Real.sqrt (Y.metric.inner (normalPair (I := I) Y x y).1
        (normalTangent (I := I) Y x z).snd
        (normalTangent (I := I) Y x z).snd) <
      expDiffeoRadius (I := I) Y.metric (normal_enorm (I := I) Y)
        (normalPair (I := I) Y x y).1 →
    diagExpInv (I := I) Y.metric (normal_enorm (I := I) Y) x
        (normalPair (I := I) Y x y) =
      normalTangent (I := I) Y x z := by
  let _ := hconn
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : ConnectedSpace Y.M := hconn
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Y.M := Manifold.metrizableSpace I Y.M
  let : T3Space Y.M := inferInstance
  let : RiemannianBundle (fun p : Y.M ↦ TangentSpace I p) :=
    Y.riemBundle (I := I)
  let : (p : Y.M) → InnerProductSpace Real (TangentSpace I p) :=
    Y.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun p : Y.M ↦ TangentSpace I p) := Y.riemBundle_cont (I := I)
  let : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  intro hdiag hproj hintr hsmallInv hsmallTan
  let pair := normalPair (I := I) Y x y
  let tangent := normalTangent (I := I) Y x z
  let inv := diagExpInv (I := I) Y.metric (normal_enorm (I := I) Y) x pair
  have hbase : pair.1 = tangent.proj := by
    have hfst := congrArg Prod.fst hdiag
    simpa only [pair, tangent, diagExp_fst] using hfst
  have htanIntr : expMapIntrinsic (I := I) Y.metric
      (normal_enorm (I := I) Y) pair.1 tangent.snd = pair.2 := by
    have hsnd := congrArg Prod.snd hdiag
    rw [diagExp_snd, ← hbase] at hsnd
    exact hsnd.symm
  have hInvSrc := expDiffeo_mem_of_lt (I := I) Y.metric
    (normal_enorm (I := I) Y) pair.1 hsmallInv
  have hInvExp : expMapDiffeo (I := I) Y.metric pair.1 inv.snd = pair.2 :=
    (expDiffeo_eq_intr (I := I) Y.metric (normal_enorm (I := I) Y)
      pair.1 hsmallInv).trans hintr
  have hInvChart :=
    (expMapDiffeo (I := I) Y.metric pair.1).left_inv' hInvSrc
  rw [hInvExp] at hInvChart
  have hTanSrc := expDiffeo_mem_of_lt (I := I) Y.metric
    (normal_enorm (I := I) Y) pair.1 hsmallTan
  have hTanExp : expMapDiffeo (I := I) Y.metric pair.1 tangent.snd = pair.2 :=
    (expDiffeo_eq_intr (I := I) Y.metric (normal_enorm (I := I) Y)
      pair.1 hsmallTan).trans htanIntr
  have hTanChart :=
    (expMapDiffeo (I := I) Y.metric pair.1).left_inv' hTanSrc
  rw [hTanExp] at hTanChart
  refine TotalSpace.ext (hproj.trans hbase) ?_
  exact heq_of_eq (hInvChart.symm.trans hTanChart)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem chart_launch_mfd
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) {x : Y.M}
    (c : NormalChartAt (I := I) Y x) {Z : Real → E × E}
    (hZat :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : SigmaCompactSpace Y.M := Y.sigmaCompact
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      HasDerivAt Z (PhaseFlow.phaseField (c.accel Y.metric) (Z 0)) 0)
    (hpos :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      (Z 0).1 ∈ Metric.ball (0 : E) c.radius) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    mfderiv 𝓘(Real, Real) I
        (fun t : Real ↦ c.hom (Z t).1) 0 1 =
      mfderiv 𝓘(Real, E) I c.hom (Z 0).1 (Z 0).2 := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let gamma : Real → E := fun t ↦ (Z t).1
  have hgammaDeriv : HasDerivAt gamma (Z 0).2 0 := by
    have hfst := (hZat.hasFDerivAt.fst).hasDerivAt
    simpa only [gamma, PhaseFlow.phaseField, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.toSpanSingleton_apply,
      one_smul] using hfst
  have hgammaMd : MDifferentiableAt 𝓘(Real, Real) 𝓘(Real, E) gamma 0 := by
    rw [mdifferentiableAt_iff_differentiableAt]
    exact hgammaDeriv.differentiableAt
  have hExpMd : MDifferentiableAt 𝓘(Real, E) I c.hom (Z 0).1 :=
    ((c.smooth_to (Z 0).1 hpos).contMDiffAt
      (Metric.isOpen_ball.mem_nhds hpos)).mdifferentiableAt (by simp)
  have hgammaMfd :
      mfderiv 𝓘(Real, Real) 𝓘(Real, E) gamma 0 1 = (Z 0).2 := by
    rw [mfderiv_eq_fderiv]
    exact (fderiv_apply_one_eq_deriv (f := gamma) (x := (0 : Real))).trans
      hgammaDeriv.deriv
  have hcomp := mfderiv_comp_apply
    (I := 𝓘(Real, Real)) (I' := 𝓘(Real, E)) (I'' := I)
    (g := c.hom) (f := gamma) (x := (0 : Real)) hExpMd hgammaMd (1 : Real)
  change mfderiv 𝓘(Real, Real) I (fun t : Real ↦ c.hom (Z t).1) 0 1 =
    mfderiv 𝓘(Real, E) I c.hom (gamma 0)
      (mfderiv 𝓘(Real, Real) 𝓘(Real, E) gamma 0 1) at hcomp
  calc
    mfderiv 𝓘(Real, Real) I
        (fun t : Real ↦ c.hom (Z t).1) 0 1 =
      mfderiv 𝓘(Real, E) I c.hom (gamma 0)
        (mfderiv 𝓘(Real, Real) 𝓘(Real, E) gamma 0 1) := by
      simpa only [gamma, Function.comp_apply] using hcomp
    _ = mfderiv 𝓘(Real, E) I c.hom (Z 0).1 (Z 0).2 := by
      rw [hgammaMfd]

theorem chart_end_eq_intr
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) (c : NormalChartAt (I := I) Y x)
    {r : Real} {R : NNReal} {Z : Real → E × E}
    (hrQuarter :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      Metric.ball (0 : E) r ⊆ Metric.ball (0 : E) (c.radius / 4))
    (hZcont : ContinuousOn Z (Icc (-1) 1))
    (hZwithin :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : SigmaCompactSpace Y.M := Y.sigmaCompact
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      ∀ t ∈ Icc (-1) 1, HasDerivWithinAt Z
        (PhaseFlow.phaseField (c.accel Y.metric) (Z t))
        (Icc (-1) 1) t)
    (hZmem : ∀ t ∈ Icc (-1) 1, Z t ∈ normalPhaseBox r R) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : ConnectedSpace Y.M := hconn
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace Y.M :=
      Manifold.metrizableSpace I Y.M
    letI : T3Space Y.M := inferInstance
    letI : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
      Y.riemBundle (I := I)
    letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun y : Y.M ↦ TangentSpace I y) := Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
    c.hom (Z 1).1 =
      expMapIntrinsic (I := I) Y.metric (normal_enorm (I := I) Y)
        (c.hom (Z 0).1)
        (mfderiv 𝓘(Real, Real) I
          (fun t : Real ↦ c.hom (Z t).1) 0 1) := by
  let _ := hconn
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : ConnectedSpace Y.M := hconn
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  let : T3Space Y.M := inferInstance
  let : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
    Y.riemBundle (I := I)
  let : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : Y.M ↦ TangentSpace I y) := Y.riemBundle_cont (I := I)
  let : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  let gamma : Real → E := fun t ↦ (Z t).1
  let Gamma : Real → Y.M := fun t ↦ c.hom (gamma t)
  have hright : ∀ t ∈ Ico (-1) 1, HasDerivWithinAt Z
      (PhaseFlow.phaseField (c.accel Y.metric) (Z t)) (Ici t) t := by
    intro t ht
    exact Analysis.ODE.Flow.hasDerivWithinAt_Ici_of_Icc
      (hZwithin t ⟨ht.1, ht.2.le⟩) ht
  have hZsmooth : ContDiffOn Real ∞ Z (Ioo (-1) 1) :=
    chartFlow_contDiff (I := I) Y.metric c (by norm_num) hZcont hright
  have hgamma : ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) ∞ gamma
      (Ioo (-1) 1) := by
    rw [contMDiffOn_iff_contDiffOn]
    exact hZsmooth.fst
  have hZat : ∀ t ∈ Ioo (-1) 1, HasDerivAt Z
      (PhaseFlow.phaseField (c.accel Y.metric) (Z t)) t := by
    intro t ht
    exact (hZwithin t (Ioo_subset_Icc_self ht)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)
  have hgeo : Geodesic.IsGeodesicOn (I := 𝓘(Real, E))
      (c.totalMetric Y.metric) gamma (Ioo (-1) 1) := by
    simpa only [gamma] using
      chartGeoOn_of_phase (I := I) Y.metric c isOpen_Ioo hZat
  have hmem : ∀ t ∈ Ioo (-1) 1, gamma t ∈ (c.inner : Set E) := by
    intro t ht
    exact hrQuarter (hZmem t (Ioo_subset_Icc_self ht)).1
  have hGammaGeo : Geodesic.IsGeodesicOn (I := I) Y.metric Gamma
      (Ioo (-1) 1) := by
    simpa only [Gamma, gamma] using
      c.geo_map Y.metric gamma (Ioo (-1) 1) isOpen_Ioo hmem hgamma hgeo
  have hGammaCont : ContinuousOn Gamma (Icc (-1) 1) := by
    apply c.smooth_to.continuousOn.comp hZcont.fst
    intro t ht
    exact c.inner_subset (hrQuarter (hZmem t ht).1)
  simpa only [Gamma, gamma] using
    (geo_end_eq_intr (I := I) Y.metric (normal_enorm (I := I) Y)
      (Gamma 0)
      (mfderiv 𝓘(Real, Real) I Gamma 0 1)
      hGammaCont hGammaGeo rfl rfl)

theorem chart_end_eq_diag
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) (c : NormalChartAt (I := I) Y x)
    {r : Real} {R : NNReal} {Z : Real → E × E}
    (hrQuarter :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      Metric.ball (0 : E) r ⊆ Metric.ball (0 : E) (c.radius / 4))
    (hZcont : ContinuousOn Z (Icc (-1) 1))
    (hZwithin :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : SigmaCompactSpace Y.M := Y.sigmaCompact
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      ∀ t ∈ Icc (-1) 1, HasDerivWithinAt Z
        (PhaseFlow.phaseField (c.accel Y.metric) (Z t))
        (Icc (-1) 1) t)
    (hZmem : ∀ t ∈ Icc (-1) 1, Z t ∈ normalPhaseBox r R) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : ConnectedSpace Y.M := hconn
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace Y.M :=
      Manifold.metrizableSpace I Y.M
    letI : T3Space Y.M := inferInstance
    letI : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
      Y.riemBundle (I := I)
    letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun y : Y.M ↦ TangentSpace I y) := Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
    normalPair (I := I) Y x ((Z 0).1, (Z 1).1) (c := c) =
      diagExp (I := I) Y.metric (normal_enorm (I := I) Y)
        (normalTangent (I := I) Y x (Z 0) (c := c)) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : ConnectedSpace Y.M := hconn
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  let : T3Space Y.M := inferInstance
  let : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
    Y.riemBundle (I := I)
  let : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : Y.M ↦ TangentSpace I y) := Y.riemBundle_cont (I := I)
  let : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  have h0 : (0 : Real) ∈ Icc (-1) 1 := by norm_num
  have hZat : HasDerivAt Z
      (PhaseFlow.phaseField (c.accel Y.metric) (Z 0)) 0 :=
    (hZwithin 0 h0).hasDerivAt (Icc_mem_nhds (by norm_num) (by norm_num))
  have hpos : (Z 0).1 ∈ Metric.ball (0 : E) c.radius :=
    c.inner_subset (hrQuarter (hZmem 0 h0).1)
  have hlaunch := chart_launch_mfd (I := I) Y c hZat hpos
  have hend := chart_end_eq_intr (I := I) Y hcomplete hconn x c
    hrQuarter hZcont hZwithin hZmem
  rw [hlaunch] at hend
  rw [normalPair, normalTangent, diagExp_apply]
  exact Prod.ext rfl hend

theorem exists_chart_diag
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) (c : NormalChartAt (I := I) Y x)
    (b :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : SigmaCompactSpace Y.M := Y.sigmaCompact
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      c.MetricBounds Y.metric)
    {r : Real} (hr : 0 < r)
    (hrMetric :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      Metric.ball (0 : E) r ⊆ Metric.ball (0 : E) b.radius)
    (hrQuarter :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      Metric.ball (0 : E) r ⊆ Metric.ball (0 : E) (c.radius / 4)) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : IsManifold I 1 Y.M := IsManifold.of_le
      (I := I) (M := Y.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : ConnectedSpace Y.M := hconn
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : TopologicalSpace.MetrizableSpace Y.M :=
      Manifold.metrizableSpace I Y.M
    letI : T3Space Y.M := inferInstance
    letI : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
      Y.riemBundle (I := I)
    letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
      Y.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun y : Y.M ↦ TangentSpace I y) := Y.riemBundle_cont (I := I)
    letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
    letI : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
    ∃ (q : NNReal) (Φ : (E × E) → Real → E × E)
        (e : OpenPartialHomeomorph (E × E) (E × E)) (δ : Real),
      0 < q ∧
      4 * (q : Real) < r ∧
      (∀ z ∈ Metric.closedBall (0 : E × E) q, Φ z 0 = z) ∧
      (∀ z ∈ Metric.closedBall (0 : E × E) q,
        ContinuousOn (Φ z) (Icc (-1) 1)) ∧
      (∀ z ∈ Metric.closedBall (0 : E × E) q, ∀ t ∈ Icc (-1) 1,
        HasDerivWithinAt (Φ z)
          (PhaseFlow.phaseField (c.accel Y.metric) (Φ z t))
          (Icc (-1) 1) t) ∧
      (∀ z ∈ Metric.closedBall (0 : E × E) q, ∀ t ∈ Ioo (-1) 1,
        HasDerivAt (Φ z)
          (PhaseFlow.phaseField (c.accel Y.metric) (Φ z t)) t) ∧
      (∀ z ∈ Metric.closedBall (0 : E × E) q, ∀ t ∈ Icc (-1) 1,
        Φ z t ∈ normalPhaseBox r (2 * q)) ∧
      Φ 0 1 = 0 ∧
      ApproximatesLinearOn (fun z ↦ (z.1, (Φ z 1).1)) PhaseFlow.freeDiag
        (Metric.closedBall (0 : E × E) q)
        (PhaseFlow.phaseErr (chartPhaseK Y.metric b (2 * q))) ∧
      ContDiffOn Real ∞ (fun z ↦ (z.1, (Φ z 1).1))
        (Metric.ball (0 : E × E) q) ∧
      0 < δ ∧
      e.source = Metric.ball (0 : E × E) q ∧
      (e : E × E → E × E) = (fun z ↦ (z.1, (Φ z 1).1)) ∧
      Metric.closedBall ((fun z ↦ (z.1, (Φ z 1).1)) 0) δ ⊆ e.target ∧
      δ = ((‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊⁻¹ -
          PhaseFlow.phaseErr (chartPhaseK Y.metric b (2 * q)) : NNReal) : Real) *
        ((q : Real) / 2) ∧
      ContDiffOn Real ∞ e.symm e.target ∧
      ∀ z ∈ Metric.closedBall (0 : E × E) q,
        normalPair (I := I) Y x (e z) (c := c) =
          diagExp (I := I) Y.metric (normal_enorm (I := I) Y)
            (normalTangent (I := I) Y x z (c := c)) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : ConnectedSpace Y.M := hconn
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  let : T3Space Y.M := inferInstance
  let : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
    Y.riemBundle (I := I)
  let : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : Y.M ↦ TangentSpace I y) := Y.riemBundle_cont (I := I)
  let : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  obtain ⟨q, hq, hqWide, hqAccel, herr⟩ :=
    exists_chart_biq (I := I) Y.metric b hr
  have hqRadius : 4 * (q : Real) < r := by nlinarith [hqWide]
  obtain ⟨Φ, hΦ0, hΦcont, hΦwithin, hΦat, hΦbox, hΦzero,
      happrox, hΦsmooth⟩ :=
    exists_chartBiflow (I := I) Y.metric c b hrMetric hrQuarter q hq
      hqWide hqAccel
  obtain ⟨e, δ, hδ, hsource, hcoe, htarget, hδeq⟩ :=
    PhaseFlow.exists_quant_inv hq happrox herr
  have happroxOpen : ApproximatesLinearOn
      (fun z ↦ (z.1, (Φ z 1).1))
      (PhaseFlow.freeDiagCLE (E := E) : (E × E) →L[Real] (E × E))
      (Metric.ball (0 : E × E) q)
      (PhaseFlow.phaseErr (chartPhaseK Y.metric b (2 * q))) := by
    simpa only [PhaseFlow.freeDiagCLE_coe] using
      happrox.mono_set Metric.ball_subset_closedBall
  have hinvSmooth : ContDiffOn Real ∞ e.symm e.target :=
    PhaseFlow.inv_smooth_of_approx happroxOpen (Or.inr herr)
      Metric.isOpen_ball hΦsmooth e hsource hcoe
  refine ⟨q, Φ, e, δ, hq, hqRadius, hΦ0, hΦcont, hΦwithin, hΦat,
    hΦbox, hΦzero, happrox, hΦsmooth, hδ, hsource, hcoe, htarget, hδeq,
    hinvSmooth, ?_⟩
  intro z hz
  have hdiag := chart_end_eq_diag (I := I) Y hcomplete hconn x c
    hrQuarter (hΦcont z hz) (hΦwithin z hz) (hΦbox z hz)
  rw [hcoe]
  simpa only [hΦ0 z hz] using hdiag

theorem exists_chart_diag_of
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) (c : NormalChartAt (I := I) Y x)
    (b :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : SigmaCompactSpace Y.M := Y.sigmaCompact
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      c.MetricBounds Y.metric)
    {r : Real}
    (hrMetric :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      Metric.ball (0 : E) r ⊆ Metric.ball (0 : E) b.radius)
    (hrQuarter :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      Metric.ball (0 : E) r ⊆ Metric.ball (0 : E) (c.radius / 4))
    (q : NNReal) (hq : 0 < q) (hqWide : 6 * (q : Real) < r)
    (hqAccel :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : SigmaCompactSpace Y.M := Y.sigmaCompact
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      3 * b.C 1 * (2 * (q : Real)) ^ 2 ≤
        (2 / 3 : Real) * (q : Real))
    (herr :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : SigmaCompactSpace Y.M := Y.sigmaCompact
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      PhaseFlow.phaseErr (chartPhaseK Y.metric b (2 * q)) <
        ‖((PhaseFlow.freeDiagCLE (E := E)).symm :
          (E × E) →L[Real] (E × E))‖₊⁻¹) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ∃ (δ : Real) (e : OpenPartialHomeomorph (E × E) (E × E)),
      0 < δ ∧
      δ = ((‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊⁻¹ -
          PhaseFlow.phaseErr (chartPhaseK Y.metric b (2 * q)) : NNReal) : Real) *
        ((q : Real) / 2) ∧
      IsNormalDiag (I := I) Y hcomplete hconn x q δ e (c := c) ∧
      NormalDiagFence (I := I) Y x q e (c := c) ∧
      ApproximatesLinearOn
        (e.symm : E × E → E × E)
        ((PhaseFlow.freeDiagCLE (E := E)).symm :
          (E × E) →L[Real] (E × E))
        e.target
        (‖((PhaseFlow.freeDiagCLE (E := E)).symm :
            (E × E) →L[Real] (E × E))‖₊ *
          (‖((PhaseFlow.freeDiagCLE (E := E)).symm :
            (E × E) →L[Real] (E × E))‖₊⁻¹ -
              PhaseFlow.phaseErr (chartPhaseK Y.metric b (2 * q)))⁻¹ *
          PhaseFlow.phaseErr (chartPhaseK Y.metric b (2 * q))) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : ConnectedSpace Y.M := hconn
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  let : T3Space Y.M := inferInstance
  let : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
    Y.riemBundle (I := I)
  let : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun y : Y.M ↦ TangentSpace I y) := Y.riemBundle_cont (I := I)
  let : EMetricSpace Y.M := Y.emetricSpace (I := I)
  let : CompleteSpace Y.M := MetricComplete.complete (I := I) Y hcomplete
  obtain ⟨Φ, hΦ0, hΦcont, hΦwithin, _hΦat, hΦbox, hΦzero,
      happrox, hΦsmooth⟩ :=
    exists_chartBiflow (I := I) Y.metric c b hrMetric hrQuarter q hq
      hqWide hqAccel
  obtain ⟨e, δ, hδ, hsource, hcoe, htarget, hδeq, hinvApprox⟩ :=
    PhaseFlow.exists_quant_inv_bi hq happrox herr
  have happroxOpen : ApproximatesLinearOn
      (fun z ↦ (z.1, (Φ z 1).1))
      (PhaseFlow.freeDiagCLE (E := E) : (E × E) →L[Real] (E × E))
      (Metric.ball (0 : E × E) q)
      (PhaseFlow.phaseErr (chartPhaseK Y.metric b (2 * q))) := by
    simpa only [PhaseFlow.freeDiagCLE_coe] using
      happrox.mono_set Metric.ball_subset_closedBall
  have hinvSmooth : ContDiffOn Real ∞ e.symm e.target :=
    PhaseFlow.inv_smooth_of_approx happroxOpen (Or.inr herr)
      Metric.isOpen_ball hΦsmooth e hsource hcoe
  have heZero : e 0 = 0 := by
    rw [hcoe]
    simp only [Prod.fst_zero, hΦzero]
    rfl
  have heSmooth : ContDiffOn Real ∞ (e : E × E → E × E) e.source := by
    rw [hsource, hcoe]
    exact hΦsmooth
  have htargetE : Metric.closedBall (e 0) δ ⊆ e.target := by
    simpa only [hcoe] using htarget
  have htarget' : Metric.closedBall (0 : E × E) δ ⊆ e.target := by
    simpa only [heZero] using htargetE
  have hdiag : ∀ z ∈ Metric.closedBall (0 : E × E) q,
      normalPair (I := I) Y x (e z) (c := c) =
        diagExp (I := I) Y.metric (normal_enorm (I := I) Y)
          (normalTangent (I := I) Y x z (c := c)) := by
    intro z hz
    have hzdiag := chart_end_eq_diag (I := I) Y hcomplete hconn x c
      hrQuarter (hΦcont z hz) (hΦwithin z hz) (hΦbox z hz)
    rw [hcoe]
    simpa only [hΦ0 z hz] using hzdiag
  have hIsDiag :
      IsNormalDiag (I := I) Y hcomplete hconn x q δ e (c := c) := by
    change e.source = Metric.ball (0 : E × E) q ∧
      e 0 = 0 ∧
      ContDiffOn Real ∞ (e : E × E → E × E) e.source ∧
      Metric.closedBall (0 : E × E) δ ⊆ e.target ∧
      ContDiffOn Real ∞ e.symm e.target ∧
      ∀ z ∈ Metric.closedBall (0 : E × E) q,
        normalPair (I := I) Y x (e z) (c := c) =
          diagExp (I := I) Y.metric (normal_enorm (I := I) Y)
            (normalTangent (I := I) Y x z (c := c))
    exact ⟨hsource, heZero, heSmooth, htarget', hinvSmooth, hdiag⟩
  have hrChart : Metric.ball (0 : E) r ⊆ Metric.ball (0 : E) c.radius := by
    intro z hz
    exact Metric.ball_subset_ball (by nlinarith [c.radius_pos]) (hrQuarter hz)
  have hfence : NormalDiagFence (I := I) Y x q e (c := c) := by
    intro z hz
    have hzNorm : ‖z‖ ≤ (q : Real) := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    have hqr : (q : Real) < r := by nlinarith [hqWide]
    have hzFirst : z.1 ∈ Metric.ball (0 : E) r := by
      rw [Metric.mem_ball, dist_zero_right]
      exact (norm_fst_le z).trans_lt (hzNorm.trans_lt hqr)
    have htime : (1 : Real) ∈ Set.Icc (-1) 1 := by norm_num
    have hzEnd : (Φ z 1).1 ∈ Metric.ball (0 : E) r :=
      (hΦbox z hz 1 htime).1
    rw [hcoe]
    exact ⟨hrChart hzFirst, hrChart hzFirst, hrChart hzEnd⟩
  exact ⟨δ, e, hδ, hδeq, hIsDiag, hfence, hinvApprox⟩

theorem exists_chart_diag_at
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (x : Y.M) (c : NormalChartAt (I := I) Y x)
    (b :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : SigmaCompactSpace Y.M := Y.sigmaCompact
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      c.MetricBounds Y.metric)
    {r : Real} (hr : 0 < r)
    (hrMetric :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      Metric.ball (0 : E) r ⊆ Metric.ball (0 : E) b.radius)
    (hrQuarter :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      Metric.ball (0 : E) r ⊆ Metric.ball (0 : E) (c.radius / 4)) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ∃ (q : NNReal) (δ : Real)
        (e : OpenPartialHomeomorph (E × E) (E × E)),
      0 < q ∧
      4 * (q : Real) < r ∧
      0 < δ ∧
      δ = ((‖((PhaseFlow.freeDiagCLE (E := E)).symm :
        (E × E) →L[Real] (E × E))‖₊⁻¹ -
          PhaseFlow.phaseErr (chartPhaseK Y.metric b (2 * q)) : NNReal) : Real) *
        ((q : Real) / 2) ∧
      IsNormalDiag (I := I) Y hcomplete hconn x q δ e (c := c) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  obtain ⟨q, hq, hqWide, hqAccel, herr⟩ :=
    exists_chart_biq (I := I) Y.metric b hr
  obtain ⟨δ, e, hδ, hδeq, hdiag, _hfence, _hinvApprox⟩ :=
    exists_chart_diag_of (I := I) Y hcomplete hconn x c b hrMetric
      hrQuarter q hq hqWide hqAccel herr
  exact ⟨q, δ, e, hq, by nlinarith [hqWide], hδ, hδeq, hdiag⟩

end HCGCompactness
end DifferentialGeometry
