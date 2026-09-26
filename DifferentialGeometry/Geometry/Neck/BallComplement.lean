import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BackwardInjectivity
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Framed.BallImage
import DifferentialGeometry.Topology.Manifold.BallComplement
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalConjugateRadius

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_uniform_pathConnected_ball_complement_of_metricNoncollapsed
    {kappa K : ℝ} (hkappa : 0 < kappa) (hK : 0 ≤ K)
    (P : PointedRiemannianManifold.{u, 0, 0} I3)
    (hcomplete : MetricComplete P) (hconnected : ConnectedSpace P.M)
    (hnc : MetricNoncollapsed P kappa (Ioc 0 1))
    (hcurv : ∀ x : P.M, Tensor0SBundle.normSq0S P.metric x 4 (metricRm04At P.metric x) ≤ K) :
    ∃ r : ℝ, 0 < r ∧ ∀ p : P.M,
      IsPathConnected (riemannianBallOf P.metric p r)ᶜ := by
  let _ : ConnectedSpace P.M := hconnected
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  let _ : IsManifold I3 1 P.M := IsManifold.of_le (n := ∞) (by decide)
  let _ : RiemannianBundle (fun x : P.M => TangentSpace I3 x) := P.riemBundle
  let _ : (x : P.M) → InnerProductSpace ℝ (TangentSpace I3 x) := P.riemInner
  let _ : IsContinuousRiemannianBundle ThreeSpace (fun x : P.M => TangentSpace I3 x) :=
    P.riemBundle_cont
  let _ : EMetricSpace P.M := P.emetricSpace
  let _ : CompleteSpace P.M := hcomplete.complete
  let _ : IsRiemannianManifold I3 P.M := ⟨fun _ _ => rfl⟩
  let _ : LocallyPathConnectedSpace P.M := ChartedSpace.locallyPathConnectedSpace ThreeSpace P.M
  let hEnorm : IsMetricNorm P.metric := fun x v =>
    tensor0SBundle_enorm_eq_riemannianBundle_enorm P.metric x v
  obtain ⟨eta, heta, hinj⟩ := exists_uniform_injectivity_of_metricNoncollapsed_curvature_bound.{u}
    hkappa hK
  obtain ⟨rc, hrc, hrc1, herr⟩ := exists_uniform_local_jacobi_scale
    (Module.finrank ℝ ThreeSpace) (R := 1) (K := Real.sqrt K) one_pos (Real.sqrt_nonneg _)
  let R := min rc eta / 2
  have hR : 0 < R := half_pos (lt_min hrc heta)
  have hRrc : R ≤ rc := by dsimp [R]; linarith [min_le_left rc eta]
  have hReta : R < eta := by dsimp [R]; linarith [min_le_right rc eta]
  refine ⟨R / 2, half_pos hR, ?_⟩
  intro p
  have hlocal : IsLocalDiffeomorphOn (𝓘(ℝ, ThreeSpace)) I3 ∞
      (intrinsicFramedExp P.metric hEnorm p) (Metric.ball (0 : ThreeSpace) R) :=
    intrinsicFrame_localOn_of_local_curvature P.metric hEnorm p (Real.sqrt_nonneg _)
      (hRrc.trans hrc1) (fun y _ => Real.sqrt_le_sqrt (hcurv y))
      (fun s hs hsr => herr s hs (hsr.trans hRrc))
  have hinjective : InjOn (intrinsicFramedExp P.metric hEnorm p)
      (Metric.ball (0 : ThreeSpace) R) := by
    have h := (hinj P hcomplete hnc hcurv p).injOn_ball hcomplete hReta
    with_unfolding_all exact h
  obtain ⟨c⟩ := exists_intrinsic_ball_chart P.metric hEnorm p hlocal hinjective
  have hcball : Metric.closedBall (0 : ThreeSpace) (R / 2) ⊆ c.hom.source := by
    rw [c.source_eq]
    exact Metric.closedBall_subset_ball (half_lt_self hR)
  have hcomp := DifferentialGeometry.Topology.isPathConnected_compl_image_ball_radius
    c.hom.toOpenPartialHomeomorph
    (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace])) (half_pos hR) hcball
  have himg := c.image_ball P.metric hEnorm p (by linarith : R / 2 ≤ R)
  change IsPathConnected (c.hom '' Metric.ball (0 : ThreeSpace) (R / 2))ᶜ at hcomp
  rw [himg] at hcomp
  have hballEq : Metric.eball p (ENNReal.ofReal (R / 2)) =
      riemannianBallOf P.metric p (R / 2) := by
    ext x
    rw [Metric.mem_eball', IsRiemannianManifold.out (I := I3)]
    rw [← riemannianEDistOf_eq_riemannianEDist P.metric hEnorm]
    rfl
  rw [hballEq] at hcomp
  exact hcomp

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
