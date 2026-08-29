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
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable [T2Space (TangentBundle I M)]

private local instance : NormedAddCommGroup (E →L[Real] Real) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance : NormedSpace Real (E →L[Real] Real) :=
  ContinuousLinearMap.toNormedSpace

private local instance : NormedAddCommGroup (E →L[Real] E →L[Real] Real) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance : NormedSpace Real (E →L[Real] E →L[Real] Real) :=
  ContinuousLinearMap.toNormedSpace

namespace NormalBallChart

def ball {p : M} (c : NormalBallChart (I := I) p) : Opens E :=
  ⟨Metric.ball (0 : E) c.radius, Metric.isOpen_ball⟩

def image {p : M} (c : NormalBallChart (I := I) p) : Opens M :=
  ⟨c.restrictBall.target, c.restrictBall.open_target⟩

noncomputable def ballDiffeo {p : M}
    (c : NormalBallChart (I := I) p) :
    Diffeomorph (modelWithCornersSelf Real E) I c.ball c.image ∞ := by
  have hsub : (c.ball : Set E) ⊆ c.restrictBall.source := by
    intro z hz
    exact hz
  let V : Opens M :=
    ⟨c.restrictBall '' (c.ball : Set E), image_opens_isOpen c.restrictBall hsub⟩
  have hV : V = c.image := by
    apply Opens.ext
    change c.restrictBall '' c.restrictBall.source = c.restrictBall.target
    exact c.restrictBall.toPartialEquiv.image_source_eq_target
  rw [← hV]
  exact PartialDiffeomorph.toOpensDiffeoCross c.restrictBall hsub

omit [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
    [T2Space (TangentBundle I M)] in
private theorem ballSigma {p : M}
    (c : NormalBallChart (I := I) p) :
    SigmaCompactSpace c.ball := by
  let : LocallyCompactSpace c.ball := c.ball.2.locallyCompactSpace
  infer_instance

omit [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
    [T2Space (TangentBundle I M)] in
private theorem imageSigma {p : M}
    (c : NormalBallChart (I := I) p) :
    SigmaCompactSpace c.image := by
  let : SigmaCompactSpace c.ball := c.ballSigma
  apply isSigmaCompact_univ_iff.mp
  have hrange : Set.range (c.ballDiffeo : c.ball → c.image) = Set.univ :=
    Set.range_eq_univ.mpr c.ballDiffeo.surjective
  rw [← hrange]
  exact isSigmaCompact_range c.ballDiffeo.continuous

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
private theorem ballDiffeo_apply {p : M}
    (c : NormalBallChart (I := I) p) (z : c.ball) :
    ((c.ballDiffeo z : c.image) : M) = c.hom (z : E) := by
  change c.restrictBall (z : E) = c.hom (z : E)
  exact c.restrictBall_apply (z : E)

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
private theorem ballDiffeo_mfd {p : M}
    (c : NormalBallChart (I := I) p) (z : c.ball) (v : E) :
    mfderiv (modelWithCornersSelf Real E) I
        (c.ballDiffeo : c.ball → c.image) z v =
      mfderiv (modelWithCornersSelf Real E) I
        (fun u : E => c.hom u) (z : E) v := by
  have hΨd : MDifferentiableAt (modelWithCornersSelf Real E) I
      (c.ballDiffeo : c.ball → c.image) z :=
    c.ballDiffeo.contMDiff.contMDiffAt.mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hvalImage : MDifferentiableAt I I (Subtype.val : c.image → M) (c.ballDiffeo z) :=
    ((contMDiff_subtype_val (I := I) (U := c.image)).contMDiffAt).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hvalBall : MDifferentiableAt (modelWithCornersSelf Real E)
      (modelWithCornersSelf Real E) (Subtype.val : c.ball → E) z := by
    exact ContMDiffAt.mdifferentiableAt
      (contMDiff_subtype_val (I := modelWithCornersSelf Real E) (U := c.ball)).contMDiffAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hhomd : MDifferentiableAt (modelWithCornersSelf Real E) I
      (fun u : E => c.hom u) (z : E) :=
    (c.smooth_to.contMDiffAt (Metric.isOpen_ball.mem_nhds z.2)).mdifferentiableAt
      (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hleft : mfderiv (modelWithCornersSelf Real E) I
      (fun y : c.ball => ((c.ballDiffeo y : c.image) : M)) z =
        (mfderiv I I (Subtype.val : c.image → M) (c.ballDiffeo z)).comp
          (mfderiv (modelWithCornersSelf Real E) I
            (c.ballDiffeo : c.ball → c.image) z) :=
    mfderiv_comp z hvalImage hΨd
  have hright : mfderiv (modelWithCornersSelf Real E) I
      (fun y : c.ball => c.hom (y : E)) z =
        (mfderiv (modelWithCornersSelf Real E) I (fun u : E => c.hom u) (z : E)).comp
          (mfderiv (modelWithCornersSelf Real E) (modelWithCornersSelf Real E)
            (Subtype.val : c.ball → E) z) :=
    mfderiv_comp z hhomd hvalBall
  have hfun : (fun y : c.ball => ((c.ballDiffeo y : c.image) : M)) =
      fun y : c.ball => c.hom (y : E) := by
    funext y
    exact c.ballDiffeo_apply y
  have hfun' : (fun y : c.ball => ((c.ballDiffeo y : c.image) : M)) =ᶠ[nhds z]
      fun y : c.ball => c.hom (y : E) :=
    Filter.Eventually.of_forall (fun y => congrFun hfun y)
  have hmap : mfderiv (modelWithCornersSelf Real E) I
      (fun y : c.ball => ((c.ballDiffeo y : c.image) : M)) z =
        mfderiv (modelWithCornersSelf Real E) I
          (fun y : c.ball => c.hom (y : E)) z :=
    Filter.EventuallyEq.mfderiv_eq
      (I := modelWithCornersSelf Real E) (I' := I) hfun'
  rw [hleft] at hmap
  rw [hright] at hmap
  have hleftId :
      (mfderiv I I (Subtype.val : c.image → M) (c.ballDiffeo z)).comp
          (mfderiv (modelWithCornersSelf Real E) I
            (c.ballDiffeo : c.ball → c.image) z) =
        mfderiv (modelWithCornersSelf Real E) I
          (c.ballDiffeo : c.ball → c.image) z := by
    ext w
    exact mfderiv_subtype_val_apply (I := I) c.image (c.ballDiffeo z) _
  have hrightId :
      (mfderiv (modelWithCornersSelf Real E) I (fun u : E => c.hom u) (z : E)).comp
          (mfderiv (modelWithCornersSelf Real E) (modelWithCornersSelf Real E)
            (Subtype.val : c.ball → E) z) =
        mfderiv (modelWithCornersSelf Real E) I (fun u : E => c.hom u) (z : E) := by
    ext w
    change mfderiv (modelWithCornersSelf Real E) I (fun u : E => c.hom u) (z : E)
      (mfderiv (modelWithCornersSelf Real E) (modelWithCornersSelf Real E)
        (Subtype.val : c.ball → E) z w) = _
    rw [mfderiv_subtype_val_apply (I := modelWithCornersSelf Real E) c.ball z]
    rfl
  rw [hleftId, hrightId] at hmap
  exact DFunLike.congr_fun hmap v

noncomputable def localMetric (g : SmoothRiemannianMetric I M) {p : M}
    (c : NormalBallChart (I := I) p) :
    SmoothRiemannianMetric (modelWithCornersSelf Real E) c.ball := by
  letI : SigmaCompactSpace c.ball := c.ballSigma
  letI : SigmaCompactSpace c.image := c.imageSigma
  exact Diffeomorph.pullbackMetricCross
    (g.restrictOpen (I := I) c.image) c.ballDiffeo

omit [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
theorem localMetric_inner (g : SmoothRiemannianMetric I M) {p : M}
    (c : NormalBallChart (I := I) p) (z : c.ball) (v w : E) :
    (c.localMetric g).inner z
        ((tangentSpaceModelContinuousLinearEquiv
          (I := modelWithCornersSelf Real E) z).symm v)
        ((tangentSpaceModelContinuousLinearEquiv
          (I := modelWithCornersSelf Real E) z).symm w) =
      c.metric g z v w := by
  let : SigmaCompactSpace c.ball := c.ballSigma
  let : SigmaCompactSpace c.image := c.imageSigma
  rw [localMetric, Diffeomorph.pullbackMetricCross_inner,
    SmoothRiemannianMetric.restrictOpen_inner]
  rw [ballDiffeo_apply]
  rw [show mfderiv (modelWithCornersSelf Real E) I
      (c.ballDiffeo : c.ball → c.image) z
        ((tangentSpaceModelContinuousLinearEquiv
          (I := modelWithCornersSelf Real E) z).symm v) =
      mfderiv (modelWithCornersSelf Real E) I (fun u : E ↦ c.hom u) (z : E) v by
    simpa only [tangentSpaceModelContinuousLinearEquiv_symm_apply] using
      c.ballDiffeo_mfd z v]
  rw [show mfderiv (modelWithCornersSelf Real E) I
      (c.ballDiffeo : c.ball → c.image) z
        ((tangentSpaceModelContinuousLinearEquiv
          (I := modelWithCornersSelf Real E) z).symm w) =
      mfderiv (modelWithCornersSelf Real E) I (fun u : E ↦ c.hom u) (z : E) w by
    simpa only [tangentSpaceModelContinuousLinearEquiv_symm_apply] using
      c.ballDiffeo_mfd z w]
  rfl

noncomputable def cut {p : M}
    (c : NormalBallChart (I := I) p) : ContDiffBump (0 : E) :=
  ⟨c.radius / 4, c.radius / 2,
    div_pos c.radius_pos (by norm_num),
    by linarith [c.radius_pos]⟩

omit [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
theorem cut_smooth {p : M} (c : NormalBallChart (I := I) p) :
    ContMDiff (modelWithCornersSelf Real E)
      (modelWithCornersSelf Real Real) ∞ (c.cut : E → Real) :=
  c.cut.contDiff.contMDiff

omit [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
theorem cut_range {p : M} (c : NormalBallChart (I := I) p) (z : E) :
    c.cut z ∈ Set.Icc (0 : Real) 1 :=
  ⟨c.cut.nonneg, c.cut.le_one⟩

omit [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
theorem cut_support {p : M} (c : NormalBallChart (I := I) p) :
    tsupport (c.cut : E → Real) ⊆ (c.ball : Set E) := by
  rw [c.cut.tsupport_eq]
  change Metric.closedBall (0 : E) (c.radius / 2) ⊆
    Metric.ball (0 : E) c.radius
  exact Metric.closedBall_subset_ball (by linarith [c.radius_pos])

omit [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
theorem cut_one {p : M} (c : NormalBallChart (I := I) p)
    {z : E} (hz : z ∈ Metric.ball (0 : E) (c.radius / 4)) :
    c.cut z = 1 :=
  c.cut.one_of_mem_closedBall (Metric.ball_subset_closedBall hz)

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
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

omit [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
theorem totalMetric_inner (g : SmoothRiemannianMetric I M) {p : M}
    (c : NormalBallChart (I := I) p) (z : E)
    (hz : z ∈ Metric.ball (0 : E) (c.radius / 4)) (v w : E) :
    (c.totalMetric g).inner z
        ((tangentSpaceModelContinuousLinearEquiv
          (I := modelWithCornersSelf Real E) z).symm v)
        ((tangentSpaceModelContinuousLinearEquiv
          (I := modelWithCornersSelf Real E) z).symm w) =
      c.metric g z v w := by
  let : SigmaCompactSpace c.ball := c.ballSigma
  let : SigmaCompactSpace c.image := c.imageSigma
  have hsub := c.inner_subset
  calc
    (c.totalMetric g).inner z
        ((tangentSpaceModelContinuousLinearEquiv
          (I := modelWithCornersSelf Real E) z).symm v)
        ((tangentSpaceModelContinuousLinearEquiv
          (I := modelWithCornersSelf Real E) z).symm w) =
      (c.localMetric g).inner ⟨z, hsub hz⟩
        ((tangentSpaceModelContinuousLinearEquiv
          (I := modelWithCornersSelf Real E) (⟨z, hsub hz⟩ : c.ball)).symm v)
        ((tangentSpaceModelContinuousLinearEquiv
          (I := modelWithCornersSelf Real E) (⟨z, hsub hz⟩ : c.ball)).symm w) := by
      simpa only [totalMetric, tangentSpaceModelContinuousLinearEquiv_symm_apply] using
        bumpExtendOpen_eq_gU_on (I := modelWithCornersSelf Real E)
          (flatMetric (E := E)) c.ball (c.localMetric g)
          (c.cut : E → Real) c.cut_smooth c.cut_range c.cut_support
          (Metric.ball (0 : E) (c.radius / 4))
          (fun q hq => c.cut_one hq) hsub z hz
          ((tangentSpaceModelContinuousLinearEquiv
            (I := modelWithCornersSelf Real E) z).symm v)
          ((tangentSpaceModelContinuousLinearEquiv
            (I := modelWithCornersSelf Real E) z).symm w)
    _ = c.metric g z v w := c.localMetric_inner g ⟨z, hsub hz⟩ v w

omit [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
theorem totalMetric_eq (g : SmoothRiemannianMetric I M) {p : M}
    (c : NormalBallChart (I := I) p) (z : E)
    (hz : z ∈ Metric.ball (0 : E) (c.radius / 4)) :
    tangentBilinearFormToModel (E := E) (M := E)
        (I := modelWithCornersSelf Real E) z
        ((c.totalMetric g).inner z) = c.metric g z := by
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  exact c.totalMetric_inner g z hz v w

omit [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
theorem total_cov_const (g : SmoothRiemannianMetric I M) {p : M}
    (c : NormalBallChart (I := I) p) (z : E)
    (hz : z ∈ Metric.ball (0 : E) (c.radius / 4))
    (hco : IsCoercive (c.metric g z)) (v w : E) :
    tangentSpaceModelContinuousLinearEquiv
        (I := modelWithCornersSelf Real E) z
        ((Geometry.Connection.leviCivitaConnectionOfMetric
          (I := modelWithCornersSelf Real E)
          (c.totalMetric g) (constantModelVectorField w) z)
          ((tangentSpaceModelContinuousLinearEquiv
            (I := modelWithCornersSelf Real E) z).symm v)) =
      MetricKoszul.koszulVec (E := E) hco
        (fderiv Real (c.metric g) z) v w := by
  have hsub := c.inner_subset
  have hEq :
      (fun y : E => tangentBilinearFormToModel (E := E) (M := E)
        (I := modelWithCornersSelf Real E) y ((c.totalMetric g).inner y)) =ᶠ[nhds z]
          c.metric g := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with y hy
    exact c.totalMetric_eq g y hy
  have hdiff : DifferentiableAt Real (c.metric g) z := by
    exact ((c.metric_contDiffOn g Metric.isOpen_ball c.smooth_to).contDiffAt
      (Metric.isOpen_ball.mem_nhds (hsub hz))).differentiableAt (by simp)
  exact _root_.DifferentialGeometry.Geometry.Connection.const_cov_eq_nhds
    (c.totalMetric g) (c.metric g) hEq hdiff hco v w

omit [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
theorem total_cov_fderiv (g : SmoothRiemannianMetric I M) {p : M}
    (c : NormalBallChart (I := I) p) (z : E)
    (hz : z ∈ Metric.ball (0 : E) (c.radius / 4))
    (hco : IsCoercive (c.metric g z)) (V : E → E)
    (_hV : MDifferentiableAt (modelWithCornersSelf Real E)
      ((modelWithCornersSelf Real E).prod (modelWithCornersSelf Real E))
      (fun y : E => (⟨y, (tangentSpaceModelContinuousLinearEquiv
        (I := modelWithCornersSelf Real E) y).symm (V y)⟩ : TangentBundle
          (modelWithCornersSelf Real E) E)) z)
    (v : E) :
    tangentSpaceModelContinuousLinearEquiv
        (I := modelWithCornersSelf Real E) z
        ((Geometry.Connection.leviCivitaConnectionOfMetric
          (I := modelWithCornersSelf Real E) (c.totalMetric g)
          (fun y : E => (tangentSpaceModelContinuousLinearEquiv
            (I := modelWithCornersSelf Real E) y).symm (V y)) z)
          ((tangentSpaceModelContinuousLinearEquiv
            (I := modelWithCornersSelf Real E) z).symm v)) =
      fderiv Real V z v +
        MetricKoszul.koszulVec (E := E) hco
          (fderiv Real (c.metric g) z) v (V z) := by
  have hsub := c.inner_subset
  have hEq :
      (fun y : E => tangentBilinearFormToModel (E := E) (M := E)
        (I := modelWithCornersSelf Real E) y ((c.totalMetric g).inner y)) =ᶠ[nhds z]
          c.metric g := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with y hy
    exact c.totalMetric_eq g y hy
  have hdiff : DifferentiableAt Real (c.metric g) z := by
    exact ((c.metric_contDiffOn g Metric.isOpen_ball c.smooth_to).contDiffAt
      (Metric.isOpen_ball.mem_nhds (hsub hz))).differentiableAt (by simp)
  exact _root_.DifferentialGeometry.Geometry.Connection.cov_eq_fderiv_add
    (c.totalMetric g) (c.metric g) hEq hdiff hco V _hV v

noncomputable def accel (g : SmoothRiemannianMetric I M) {p : M}
    (c : NormalBallChart (I := I) p) (z : E × E) : E :=
  -(tangentSpaceModelContinuousLinearEquiv
      (I := modelWithCornersSelf Real E) z.1
      ((_root_.DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric
        (I := modelWithCornersSelf Real E) (c.totalMetric g)
        (constantModelVectorField z.2) z.1)
        ((tangentSpaceModelContinuousLinearEquiv
          (I := modelWithCornersSelf Real E) z.1).symm z.2)))

omit [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
@[simp] theorem accel_zero (g : SmoothRiemannianMetric I M) {p : M}
    (c : NormalBallChart (I := I) p) :
    c.accel g (0 : E × E) = 0 := by
  unfold accel
  simp only [Prod.fst_zero, Prod.snd_zero]
  rw [_root_.DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_apply]
  have hz :
      _root_.DifferentialGeometry.Geometry.Connection.leviCivitaConnectionCandidateAt
          (I := modelWithCornersSelf Real E)
          (c.totalMetric g) (constantModelVectorField (0 : E))
          (0 : E) ((tangentSpaceModelContinuousLinearEquiv
            (I := modelWithCornersSelf Real E) (0 : E)).symm 0) = 0 :=
    ContinuousLinearMap.map_zero _
  rw [hz]
  have hzero : tangentSpaceModelContinuousLinearEquiv
      (I := modelWithCornersSelf Real E) (0 : E) (0 : TangentSpace
        (modelWithCornersSelf Real E) (0 : E)) = 0 :=
    (tangentSpaceModelContinuousLinearEquiv
      (I := modelWithCornersSelf Real E) (0 : E)).map_zero
  rw [hzero, neg_zero]

omit [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
theorem accel_eq (g : SmoothRiemannianMetric I M) {p : M}
    (c : NormalBallChart (I := I) p) (z : E × E)
    (hz : z.1 ∈ Metric.ball (0 : E) (c.radius / 4))
    (hco : IsCoercive (c.metric g z.1)) :
    c.accel g z =
      -MetricKoszul.koszulVec (E := E) hco
        (fderiv Real (c.metric g) z.1) z.2 z.2 := by
  unfold accel
  rw [c.total_cov_const g z.1 hz hco z.2 z.2]

end NormalBallChart
end NormalCoordinates
end Riemannian
end Geometry
end DifferentialGeometry
