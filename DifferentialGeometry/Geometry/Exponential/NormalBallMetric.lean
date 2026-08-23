import DifferentialGeometry.Topology.Manifold.PartialDiffeomorphOpens
import DifferentialGeometry.Geometry.Connection.LeviCivita.MetricKoszul
import DifferentialGeometry.Geometry.Exponential.NormalBallChart
import DifferentialGeometry.Geometry.Metric.BumpExtend
import DifferentialGeometry.Geometry.Metric.PullbackCross
import Mathlib.Geometry.Manifold.Riemannian.Basic

set_option autoImplicit false

noncomputable section

universe u uE uH

open Bundle Set TopologicalSpace
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace NormalCoordinates

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable [T2Space (TangentBundle I M)]

namespace NormalBallChart

def ball {p : M} (c : NormalBallChart (I := I) p) : Opens E :=
  ⟨Metric.ball (0 : E) c.radius, Metric.isOpen_ball⟩

def image {p : M} (c : NormalBallChart (I := I) p) : Opens M :=
  ⟨c.restrictBall.target, c.restrictBall.open_target⟩

noncomputable def ballDiffeo {p : M}
    (c : NormalBallChart (I := I) p) :
    Diffeomorph (modelWithCornersSelf Real E) I c.ball c.image ∞ := by
  simpa only [ball, image] using
    PartialDiffeomorph.toOpensDiffeoCross c.restrictBall
      (by
        intro z hz
        exact hz)

@[implicit_reducible] private noncomputable def ballSigma {p : M}
    (c : NormalBallChart (I := I) p) :
    SigmaCompactSpace c.ball := by
  letI : LocallyCompactSpace c.ball := c.ball.2.locallyCompactSpace
  infer_instance

@[implicit_reducible] private noncomputable def imageSigma {p : M}
    (c : NormalBallChart (I := I) p) :
    SigmaCompactSpace c.image := by
  letI : SigmaCompactSpace c.ball := c.ballSigma
  apply isSigmaCompact_univ_iff.mp
  have hrange : Set.range (c.ballDiffeo : c.ball → c.image) = Set.univ :=
    Set.range_eq_univ.mpr c.ballDiffeo.surjective
  rw [← hrange]
  exact isSigmaCompact_range c.ballDiffeo.continuous

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
private theorem ballDiffeo_apply {p : M}
    (c : NormalBallChart (I := I) p) (z : c.ball) :
    ((c.ballDiffeo z : c.image) : M) = c.hom (z : E) := by
  change c.restrictBall (z : E) = c.hom (z : E)
  exact c.restrictBall_apply (z : E)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
private theorem ballDiffeo_mfd {p : M}
    (c : NormalBallChart (I := I) p) (z : c.ball) (v : E) :
    mfderiv (modelWithCornersSelf Real E) I
        (c.ballDiffeo : c.ball → c.image) z v =
      mfderiv (modelWithCornersSelf Real E) I
        (fun u : E => c.hom u) (z : E) v := by
  have h := PartialDiffeomorph.mfderiv_toOpensDiffeoCross
    c.restrictBall (by
      intro q hq
      exact hq) z v
  simpa only [ballDiffeo, restrictBall_apply] using h

noncomputable def localMetric (g : SmoothRiemannianMetric I M) {p : M}
    (c : NormalBallChart (I := I) p) :
    SmoothRiemannianMetric (modelWithCornersSelf Real E) c.ball := by
  letI : SigmaCompactSpace c.ball := c.ballSigma
  letI : SigmaCompactSpace c.image := c.imageSigma
  exact Diffeomorph.pullbackMetricCross
    (g.restrictOpen (I := I) c.image) c.ballDiffeo

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
theorem localMetric_inner (g : SmoothRiemannianMetric I M) {p : M}
    (c : NormalBallChart (I := I) p) (z : c.ball) (v w : E) :
    (c.localMetric g).inner z v w = c.metric g z v w := by
  letI : SigmaCompactSpace c.ball := c.ballSigma
  letI : SigmaCompactSpace c.image := c.imageSigma
  rw [localMetric, Diffeomorph.pullbackMetricCross_inner,
    SmoothRiemannianMetric.restrictOpen_inner]
  rw [ballDiffeo_apply, ballDiffeo_mfd, ballDiffeo_mfd]
  rfl

noncomputable def cut {p : M}
    (c : NormalBallChart (I := I) p) : ContDiffBump (0 : E) :=
  ⟨c.radius / 4, c.radius / 2,
    div_pos c.radius_pos (by norm_num),
    by linarith [c.radius_pos]⟩

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
theorem cut_smooth {p : M} (c : NormalBallChart (I := I) p) :
    ContMDiff (modelWithCornersSelf Real E)
      (modelWithCornersSelf Real Real) ∞ (c.cut : E → Real) :=
  c.cut.contDiff.contMDiff

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
theorem cut_range {p : M} (c : NormalBallChart (I := I) p) (z : E) :
    c.cut z ∈ Set.Icc (0 : Real) 1 :=
  ⟨c.cut.nonneg, c.cut.le_one⟩

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
theorem cut_support {p : M} (c : NormalBallChart (I := I) p) :
    tsupport (c.cut : E → Real) ⊆ (c.ball : Set E) := by
  rw [c.cut.tsupport_eq]
  change Metric.closedBall (0 : E) (c.radius / 2) ⊆
    Metric.ball (0 : E) c.radius
  exact Metric.closedBall_subset_ball (by linarith [c.radius_pos])

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
theorem cut_one {p : M} (c : NormalBallChart (I := I) p)
    {z : E} (hz : z ∈ Metric.ball (0 : E) (c.radius / 4)) :
    c.cut z = 1 :=
  c.cut.one_of_mem_closedBall (Metric.ball_subset_closedBall hz)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
theorem inner_subset {p : M} (c : NormalBallChart (I := I) p) :
    Metric.ball (0 : E) (c.radius / 4) ⊆ (c.ball : Set E) :=
  Metric.ball_subset_ball (by linarith [c.radius_pos])

private noncomputable def flatMetric :
    SmoothRiemannianMetric (modelWithCornersSelf Real E) E where
  inner := (riemannianMetricVectorSpace E).inner
  symm := (riemannianMetricVectorSpace E).symm
  pos := (riemannianMetricVectorSpace E).pos
  isVonNBounded := (riemannianMetricVectorSpace E).isVonNBounded
  contMDiff := (riemannianMetricVectorSpace E).contMDiff.of_le le_top

noncomputable def totalMetric (g : SmoothRiemannianMetric I M) {p : M}
    (c : NormalBallChart (I := I) p) :
    SmoothRiemannianMetric (modelWithCornersSelf Real E) E := by
  letI : SigmaCompactSpace c.ball := c.ballSigma
  exact (flatMetric (E := E)).bumpExtendOpen c.ball (c.localMetric g)
    (c.cut : E → Real) c.cut_smooth c.cut_range c.cut_support

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
theorem totalMetric_inner (g : SmoothRiemannianMetric I M) {p : M}
    (c : NormalBallChart (I := I) p) (z : E)
    (hz : z ∈ Metric.ball (0 : E) (c.radius / 4)) (v w : E) :
    (c.totalMetric g).inner z v w = c.metric g z v w := by
  letI : SigmaCompactSpace c.ball := c.ballSigma
  letI : SigmaCompactSpace c.image := c.imageSigma
  have hsub := c.inner_subset
  calc
    (c.totalMetric g).inner z v w =
        (c.localMetric g).inner ⟨z, hsub hz⟩ v w := by
      simpa only [totalMetric] using
        bumpExtendOpen_eq_gU_on (I := modelWithCornersSelf Real E)
          (flatMetric (E := E)) c.ball (c.localMetric g)
          (c.cut : E → Real) c.cut_smooth c.cut_range c.cut_support
          (Metric.ball (0 : E) (c.radius / 4))
          (fun q hq => c.cut_one hq) hsub z hz v w
    _ = c.metric g z v w := c.localMetric_inner g ⟨z, hsub hz⟩ v w

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
theorem totalMetric_eq (g : SmoothRiemannianMetric I M) {p : M}
    (c : NormalBallChart (I := I) p) (z : E)
    (hz : z ∈ Metric.ball (0 : E) (c.radius / 4)) :
    (c.totalMetric g).inner z = c.metric g z := by
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  exact c.totalMetric_inner g z hz v w

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
theorem total_cov_const (g : SmoothRiemannianMetric I M) {p : M}
    (c : NormalBallChart (I := I) p) (z : E)
    (hz : z ∈ Metric.ball (0 : E) (c.radius / 4))
    (hco : IsCoercive (c.metric g z)) (v w : E) :
    (Geometry.Connection.leviCivitaConnectionOfMetric
        (I := modelWithCornersSelf Real E)
        (c.totalMetric g) (fun _ : E => w) z) v =
      MetricKoszul.koszulVec hco
        (fderiv Real (c.metric g) z) v w := by
  have hsub := c.inner_subset
  have hEq :
      (fun y : E => (c.totalMetric g).inner y) =ᶠ[nhds z] c.metric g := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with y hy
    exact c.totalMetric_eq g y hy
  have hdiff : DifferentiableAt Real (c.metric g) z := by
    exact ((c.metric_contDiffOn g Metric.isOpen_ball c.smooth_to).contDiffAt
      (Metric.isOpen_ball.mem_nhds (hsub hz))).differentiableAt (by simp)
  exact _root_.DifferentialGeometry.Geometry.Connection.const_cov_eq_nhds
    (c.totalMetric g) (c.metric g) hEq hdiff hco v w

omit [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
omit [NeZero (Module.finrank ℝ E)] in
theorem total_cov_fderiv (g : SmoothRiemannianMetric I M) {p : M}
    (c : NormalBallChart (I := I) p) (z : E)
    (hz : z ∈ Metric.ball (0 : E) (c.radius / 4))
    (hco : IsCoercive (c.metric g z)) (V : E → E)
    (_hV : MDifferentiableAt (modelWithCornersSelf Real E)
      ((modelWithCornersSelf Real E).prod (modelWithCornersSelf Real E))
      (fun y : E => (⟨y, V y⟩ : TangentBundle
        (modelWithCornersSelf Real E) E)) z)
    (v : E) :
    (Geometry.Connection.leviCivitaConnectionOfMetric
        (I := modelWithCornersSelf Real E) (c.totalMetric g) V z) v =
      fderiv Real V z v +
        MetricKoszul.koszulVec hco
          (fderiv Real (c.metric g) z) v (V z) := by
  have hsub := c.inner_subset
  have hEq :
      (fun y : E => (c.totalMetric g).inner y) =ᶠ[nhds z] c.metric g := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with y hy
    exact c.totalMetric_eq g y hy
  have hdiff : DifferentiableAt Real (c.metric g) z := by
    exact ((c.metric_contDiffOn g Metric.isOpen_ball c.smooth_to).contDiffAt
      (Metric.isOpen_ball.mem_nhds (hsub hz))).differentiableAt (by simp)
  exact _root_.DifferentialGeometry.Geometry.Connection.cov_eq_fderiv_add
    (c.totalMetric g) (c.metric g) hEq hdiff hco V _hV v

noncomputable def accel (g : SmoothRiemannianMetric I M) {p : M}
    (c : NormalBallChart (I := I) p) (z : E × E) : E :=
  -((_root_.DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric
        (I := modelWithCornersSelf Real E)
        (c.totalMetric g) (fun _ : E => z.2) z.1) z.2)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
@[simp] theorem accel_zero (g : SmoothRiemannianMetric I M) {p : M}
    (c : NormalBallChart (I := I) p) :
    c.accel g (0 : E × E) = 0 := by
  unfold accel
  change -((_root_.DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric
      (I := modelWithCornersSelf Real E)
      (c.totalMetric g) (fun _ : E => (0 : E)) (0 : E)) (0 : E)) = 0
  rw [_root_.DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_apply]
  have hz :
      _root_.DifferentialGeometry.Geometry.Connection.leviCivitaConnectionCandidateAt
          (I := modelWithCornersSelf Real E)
          (c.totalMetric g) (fun _ : E => (0 : E))
          (0 : E) (0 : E) = 0 :=
    ContinuousLinearMap.map_zero _
  rw [hz, neg_zero]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
theorem accel_eq (g : SmoothRiemannianMetric I M) {p : M}
    (c : NormalBallChart (I := I) p) (z : E × E)
    (hz : z.1 ∈ Metric.ball (0 : E) (c.radius / 4))
    (hco : IsCoercive (c.metric g z.1)) :
    c.accel g z =
      -MetricKoszul.koszulVec hco
        (fderiv Real (c.metric g) z.1) z.2 z.2 := by
  unfold accel
  rw [c.total_cov_const g z.1 hz hco z.2 z.2]
  rfl

end NormalBallChart
end NormalCoordinates
end Riemannian
end Geometry
end DifferentialGeometry
