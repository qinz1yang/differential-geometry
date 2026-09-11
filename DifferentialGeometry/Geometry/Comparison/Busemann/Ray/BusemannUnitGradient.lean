import DifferentialGeometry.Geometry.Operator.GradientTouchingSupport
import DifferentialGeometry.Geometry.Comparison.Busemann.Ray.OppositeSumDifferentiability
import DifferentialGeometry.Geometry.Comparison.Busemann.Ray.BusemannUnitSupport

set_option autoImplicit false
noncomputable section

open Bundle Set Filter Manifold Function
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry.Geometry.Metric

section SameLine

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem intrinsic_busemann_unit_gradients_of_opposite_sum_zero
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g)
    (hRic : ∀ y : M, ∀ v : TangentSpace I y, 0 ≤ ricciTensor g y v v)
    (gamma : ℝ → M)
    (hline : ∀ s t : ℝ,
      riemannianEDistOf g (gamma s) (gamma t) = ENNReal.ofReal |s - t|)
    (hsum : ∀ y : M,
      (⨅ t : ℝ, (riemannianEDistOf g y (gamma t)).toReal - t) +
        (⨅ t : ℝ, (riemannianEDistOf g y (gamma (-t))).toReal - t) = 0) :
    let bplus : M → ℝ := fun y ↦ ⨅ t : ℝ,
      (riemannianEDistOf g y (gamma t)).toReal - t
    let bminus : M → ℝ := fun y ↦ ⨅ t : ℝ,
      (riemannianEDistOf g y (gamma (-t))).toReal - t
    MDifferentiable I 𝓘(ℝ, ℝ) bplus ∧ MDifferentiable I 𝓘(ℝ, ℝ) bminus ∧
      ∀ x : M,
        g.inner x (gradientFun g bplus x) (gradientFun g bplus x) = 1 ∧
        g.inner x (gradientFun g bminus x) (gradientFun g bminus x) = 1 := by
  let bplus : M → ℝ := fun y ↦ ⨅ t : ℝ,
    (riemannianEDistOf g y (gamma t)).toReal - t
  let bminus : M → ℝ := fun y ↦ ⨅ t : ℝ,
    (riemannianEDistOf g y (gamma (-t))).toReal - t
  obtain ⟨hplusDiff, hminusDiff⟩ :=
    intrinsic_busemann_mdifferentiable_of_opposite_sum_zero g hcomplete hRic gamma hline hsum
  have hreverse (s t : ℝ) :
      riemannianEDistOf g (gamma (-s)) (gamma (-t)) = ENNReal.ofReal |s - t| := by
    rw [hline]
    have hneg : -s - -t = -(s - t) := by ring
    rw [hneg, abs_neg]
  refine ⟨hplusDiff, hminusDiff, ?_⟩
  intro x
  obtain ⟨phi, U, hU, hxU, hphi, hphiEq, hphiUpper, _hphiLap, hphiUnit⟩ :=
    busemannFunction_exists_smooth_unit_upper_support g hcomplete hRic gamma hline x 1 one_pos
  obtain ⟨psi, V, hV, hxV, hpsi, hpsiEq, hpsiUpper, _hpsiLap, hpsiUnit⟩ :=
    busemannFunction_exists_smooth_unit_upper_support g hcomplete hRic
      (fun t : ℝ ↦ gamma (-t)) hreverse x 1 one_pos
  have hphiDiff : MDifferentiableAt I 𝓘(ℝ, ℝ) phi x :=
    ((hphi x hxU).contMDiffAt (hU.mem_nhds hxU)).mdifferentiableAt (by simp)
  have hpsiDiff : MDifferentiableAt I 𝓘(ℝ, ℝ) psi x :=
    ((hpsi x hxV).contMDiffAt (hV.mem_nhds hxV)).mdifferentiableAt (by simp)
  have hplusUpper : ∀ᶠ y in 𝓝 x, bplus y ≤ phi y := by
    filter_upwards [hU.mem_nhds hxU] with y hy
    exact hphiUpper y hy
  have hminusUpper : ∀ᶠ y in 𝓝 x, bminus y ≤ psi y := by
    filter_upwards [hV.mem_nhds hxV] with y hy
    exact hpsiUpper y hy
  have hplusGrad : gradientFun g bplus x = gradientFun g phi x :=
    DifferentialGeometry.Geometry.Operator.gradientFun_eq_of_touching_upper_support
      g (hplusDiff x) hphiDiff hphiEq hplusUpper
  have hminusGrad : gradientFun g bminus x = gradientFun g psi x :=
    DifferentialGeometry.Geometry.Operator.gradientFun_eq_of_touching_upper_support
      g (hminusDiff x) hpsiDiff hpsiEq hminusUpper
  constructor
  · rw [hplusGrad]
    exact hphiUnit
  · rw [hminusGrad]
    exact hpsiUnit

end SameLine

end DifferentialGeometry.Geometry.Metric

end
