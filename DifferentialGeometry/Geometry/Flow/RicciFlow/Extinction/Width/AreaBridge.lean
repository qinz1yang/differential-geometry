import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.LeastArea
import DifferentialGeometry.Geometry.Measure.Area.ManifoldComposition
import DifferentialGeometry.Geometry.Measure.Area.EuclideanDisk
import DifferentialGeometry.Geometry.Metric.InfinitesimalDistance

noncomputable section
open Bundle Manifold Set MeasureTheory Topology
open scoped Manifold ContDiff Topology ENNReal NNReal
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
set_option backward.isDefEq.respectTransparency false in
theorem parametricJacobian_eq_riemannianAreaDensity (g : SmoothRiemannianMetric I Q)
    (U : ℂ → Q) (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    parametricJacobian g U (Metric.closedBall (0 : ℂ) 1) z =
      Geometry.riemannianAreaDensity g U z := by
  have hs : Metric.closedBall (0 : ℂ) 1 ∈ 𝓝 z :=
    Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hz) Metric.ball_subset_closedBall
  by_cases hd : MDifferentiableAt 𝓘(ℝ, ℂ) I U z
  · have hw : MDifferentiableWithinAt 𝓘(ℝ, ℂ) I U (Metric.closedBall (0 : ℂ) 1) z :=
      hd.mdifferentiableWithinAt
    rw [parametricJacobian, if_pos hw, mfderivWithin_of_mem_nhds (f := U) hs]
    have h0 : diskBasis (0 : Fin 2) = (1 : ℂ) := by simp [diskBasis]
    have h1 : diskBasis (1 : Fin 2) = Complex.I := by simp [diskBasis]
    refine congrArg Real.sqrt ?_
    rw [show (fun i j : Fin 2 => (g.inner (U z)) (mfderiv 𝓘(ℝ, ℂ) I U z (diskBasis i))
        (mfderiv 𝓘(ℝ, ℂ) I U z (diskBasis j))) = Matrix.of (fun i j : Fin 2 =>
          (g.inner (U z)) (mfderiv 𝓘(ℝ, ℂ) I U z (diskBasis i))
            (mfderiv 𝓘(ℝ, ℂ) I U z (diskBasis j))) from rfl, Matrix.det_fin_two]
    simp only [Matrix.of_apply]
    rw [h0, h1]
    rw [g.symm (U z) (mfderiv 𝓘(ℝ, ℂ) I U z Complex.I) (mfderiv 𝓘(ℝ, ℂ) I U z (1 : ℂ))]
    ring
  · have hw : ¬ MDifferentiableWithinAt 𝓘(ℝ, ℂ) I U (Metric.closedBall (0 : ℂ) 1) z :=
      fun h => hd (h.mdifferentiableAt hs)
    rw [parametricJacobian, if_neg hw,
      Geometry.riemannianAreaDensity_eq_zero_of_not_mdifferentiableAt g hd]

theorem diskArea_eq_riemannianDiskArea (g : SmoothRiemannianMetric I Q) (u : Disk → Q) :
    diskArea g u = Geometry.riemannianDiskArea g u := by
  simp only [diskArea, diskJacobian, Geometry.riemannianDiskArea, Geometry.riemannianArea]
  refine integral_congr_ae ?_
  filter_upwards [Geometry.ae_disk_interior] with z hz
  refine (parametricJacobian_congr_on (s := Metric.closedBall (0 : ℂ) 1) g ?_
    (Metric.ball_subset_closedBall hz)).trans
    (parametricJacobian_eq_riemannianAreaDensity g (Geometry.diskExtension u) z hz)
  intro w hw
  simp only [diskExtension, dif_pos hw, Geometry.diskExtension, Function.comp_apply]
  rw [Geometry.diskRetraction_coe ⟨w, hw⟩]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
set_option backward.isDefEq.respectTransparency false in
theorem parametricJacobian_eq_zero_of_subsingleton_model (I : ModelWithCorners ℝ E H)
    (Q : Type*) [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q] [Subsingleton E]
    (g : SmoothRiemannianMetric I Q) (U : ℂ → Q) (s : Set ℂ) (z : ℂ) :
    parametricJacobian g U s z = 0 := by
  let : Subsingleton (TangentSpace I (U z)) := ‹Subsingleton E›
  have hzero : mfderivWithin 𝓘(ℝ, ℂ) I U s z = 0 := by
    ext v
    exact Subsingleton.elim _ _
  unfold parametricJacobian
  split_ifs with hd
  · rw [hzero]
    simp [Matrix.det_fin_two]
  · rfl

theorem eventuallyEq_const_of_subsingleton_model (I : ModelWithCorners ℝ E H)
    (Q : Type*) [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q] [Subsingleton E]
    {X : Type*} [TopologicalSpace X] {u : X → Q} {x : X} (hu : ContinuousAt u x) :
    u =ᶠ[𝓝 x] (fun _ => u x) := by
  let _ : Subsingleton H := subsingleton_of_subsingleton_model I ‹Subsingleton E›
  filter_upwards [hu ((chartAt H (u x)).open_source.mem_nhds (mem_chart_source H (u x)))]
    with y hy
  exact (chartAt H (u x)).injOn hy (mem_chart_source H (u x)) (Subsingleton.elim _ _)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
set_option backward.isDefEq.respectTransparency false in
theorem parametricJacobian_eq_zero_of_eventuallyEq_const (I : ModelWithCorners ℝ E H)
    (Q : Type*) [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
    (g : SmoothRiemannianMetric I Q)
    (U : ℂ → Q) {s : Set ℂ} {z : ℂ} (hs : s ∈ 𝓝 z)
    (hU : U =ᶠ[𝓝 z] fun _ => U z) : parametricJacobian g U s z = 0 := by
  have hd : MDifferentiableAt 𝓘(ℝ, ℂ) I U z :=
    hU.mdifferentiableAt_iff.mpr mdifferentiableAt_const
  have hderiv : mfderivWithin 𝓘(ℝ, ℂ) I U s z = 0 := by
    rw [mfderivWithin_of_mem_nhds (f := U) hs, hU.mfderiv_eq]
    simp
  unfold parametricJacobian
  rw [if_pos hd.mdifferentiableWithinAt, hderiv]
  simp [Matrix.det_fin_two]



end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
