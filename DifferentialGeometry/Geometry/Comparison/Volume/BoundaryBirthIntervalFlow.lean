import DifferentialGeometry.Geometry.Geodesic.Flow.VelocityLift
import DifferentialGeometry.Geometry.Geodesic.Flow.FiniteMetric
import DifferentialGeometry.Geometry.Geodesic.FiniteMetric.SmoothSpray
import DifferentialGeometry.External.TauCeti.Geometry.Manifold.IntegralCurve.Maximal

/-!
Actual velocity lifts agree with native maximal flow on their entire open geodesic interval.
The translated interval includes backward birth times without assuming completeness or exit data.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Manifold
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]
  {N : Type*} [nativeTopology : TopologicalSpace N]
  [nativeCharts : ChartedSpace E N] [nativeSmooth : IsManifold 𝓘(ℝ, E) ∞ N]
  [nativeT2 : T2Space N]

theorem boundaryBirth_interval_flow (g : SmoothRiemannianMetric 𝓘(ℝ, E) N)
    {γ : ℝ → N} {b c a : ℝ} (ha : a ∈ Ioo b c)
    (hgeo : IsGeodesicOn g γ (Ioo b c)) (hcont : ContinuousOn γ (Ioo b c)) :
    ∀ t ∈ Ioo b c,
      (DifferentialGeometry.velocityLift (I := 𝓘(ℝ, E)) γ a, t - a) ∈ g.geodesicFlowDomain ∧
        g.geodesicFlow (DifferentialGeometry.velocityLift (I := 𝓘(ℝ, E)) γ a) (t - a) =
          DifferentialGeometry.velocityLift (I := 𝓘(ℝ, E)) γ t := by
  have hcurve : IsMIntegralCurveOn (DifferentialGeometry.velocityLift (I := 𝓘(ℝ, E)) γ)
      g.geodesicSpray (Ioo b c) := by
    simpa only [g.geodesicSpray_eq_geodesicVectorField_fun] using
      isMIntegralCurveOn_velocityLift g isOpen_Ioo hgeo hcont
  have hshift : IsMIntegralCurveOn (DifferentialGeometry.velocityLift (I := 𝓘(ℝ, E)) γ ∘ (· + a))
      g.geodesicSpray (Ioo (b - a) (c - a)) := by
    convert hcurve.comp_add a using 1
    ext r
    simp only [mem_Ioo, mem_ofPred_eq, sub_lt_iff_lt_add, lt_sub_iff_add_lt]
  have hzero : (0 : ℝ) ∈ Ioo (b - a) (c - a) :=
    ⟨by linarith [ha.1], by linarith [ha.2]⟩
  have hinitial : (DifferentialGeometry.velocityLift (I := 𝓘(ℝ, E)) γ ∘ (· + a)) 0 =
      DifferentialGeometry.velocityLift (I := 𝓘(ℝ, E)) γ a := by simp
  have hinclude := hshift.subset_maximalIntegralCurveInterval hzero hinitial
  have hmatch := hshift.eqOn_maximalIntegralCurve
    ((g.contMDiff_geodesicSpray (r := ⊤)).of_le (by exact_mod_cast le_top)) hzero hinitial
  intro t ht
  have htshift : t - a ∈ Ioo (b - a) (c - a) :=
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  refine ⟨hinclude htshift, ?_⟩
  exact (hmatch htshift).trans (congrArg
    (DifferentialGeometry.velocityLift (I := 𝓘(ℝ, E)) γ) (sub_add_cancel t a))

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
