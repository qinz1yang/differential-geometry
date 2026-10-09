import DifferentialGeometry.Geometry.Collapse.LocalVolumeSequence
import DifferentialGeometry.Geometry.Collapse.RescaledLimits.PointedLimit

set_option autoImplicit false
noncomputable section
open Set Metric Filter Real
open scoped Manifold ContDiff ENNReal Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Comparison.Toponogov GC.MetricGeometry
namespace DifferentialGeometry.Geometry.Collapse
universe u v
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {Z : ℕ → Type u} [mZ : ∀ n, MetricSpace (Z n)]
  [∀ n, ChartedSpace H (Z n)] [∀ n, IsManifold I ∞ (Z n)]
  [∀ n, SigmaCompactSpace (Z n)] [∀ n, CompleteSpace (Z n)]

/-- The LC06 formulation is a specialization of the canonical LC15 producer. -/
theorem eventually_rescaled_ballVolume_lower_of_localVolume_producer
    (hdim : Module.finrank ℝ E = 3)
    (g : ∀ n, SmoothRiemannianMetric I (Z n))
    (hmetric : ∀ n a b, riemannianEDistOf (g n) a b = ENNReal.ofReal (dist a b))
    (p : ∀ n, Z n) {ρ L : ℕ → ℝ} (hρ : ∀ n, 0 < ρ n)
    (hL : Tendsto L atTop atTop)
    (hsec : ∀ n, ∀ y ∈ riemannianBallOf (g n) (p n) (L n * ρ n),
      SectionalBoundedBelowAt (g n) y (-((L n * ρ n) ^ 2)⁻¹))
    {Y : Type v} [MetricSpace Y] {x : Y}
    (hconv : @PointedGHConverges Z
      (fun n => (mZ n).rescale (ρ n)⁻¹ (inv_pos.mpr (hρ n))) Y _ p x)
    (hdimY : 2 < dimH (univ : Set Y)) :
    ∃ v : ℝ, 0 < v ∧ ∀ᶠ n in atTop, ENNReal.ofReal v ≤
      ballVolume (scaleMetric ((ρ n)⁻¹ ^ 2)
        (pow_pos (inv_pos.mpr (hρ n)) 2) (g n)) (p n) 2
 := by
  let m' : ∀ n, MetricSpace (Z n) := fun n =>
    (mZ n).rescale (ρ n)⁻¹ (inv_pos.mpr (hρ n))
  have : ∀ n, CompleteSpace (Z n) := fun n =>
    ((mZ n).rescale_completeSpace_iff (ρ n)⁻¹ (inv_pos.mpr (hρ n))).mpr inferInstance
  have hκ : ∀ n, 0 ≤ (L n ^ 2)⁻¹ := fun n => inv_nonneg.mpr (sq_nonneg _)
  have hκzero : Tendsto (fun n => (L n ^ 2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop two_ne_zero).comp hL)
  exact eventually_volume_ball_two_lower_of_growing_sectional_bound
    (fun n => scaleMetric ((ρ n)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ n)) 2) (g n))
    (fun n => riemannianEDistOf_scaleMetric_inv_sq_eq_rescale (m := mZ n)
      (g n) (hmetric n) (hρ n)) hdim hκ hκzero hL
    (fun n => sectionalBoundedBelowAt_rescaled_ball (m := mZ n)
      (g n) (hmetric n) (p n) (hρ n) (hsec n)) hconv hdimY

end DifferentialGeometry.Geometry.Collapse
