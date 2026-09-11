import DifferentialGeometry.Analysis.Elliptic.Barrier.ManifoldTouchingSupports
import DifferentialGeometry.Geometry.Comparison.Busemann.Ray.BusemannUpperSupport

set_option autoImplicit false
noncomputable section

open Bundle Set Filter Manifold Function
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
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
theorem intrinsic_busemann_mdifferentiable_of_opposite_sum_zero
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
    MDifferentiable I 𝓘(ℝ, ℝ) bplus ∧ MDifferentiable I 𝓘(ℝ, ℝ) bminus := by
  let bplus : M → ℝ := fun y ↦ ⨅ t : ℝ,
    (riemannianEDistOf g y (gamma t)).toReal - t
  let bminus : M → ℝ := fun y ↦ ⨅ t : ℝ,
    (riemannianEDistOf g y (gamma (-t))).toReal - t
  let : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
  have hminus (y : M) : bminus y = -bplus y := by
    have hy := hsum y
    change bplus y + bminus y = 0 at hy
    linarith only [hy]
  have hreverse (s t : ℝ) :
      riemannianEDistOf g (gamma (-s)) (gamma (-t)) = ENNReal.ofReal |s - t| := by
    rw [hline]
    have hneg : -s - -t = -(s - t) := by ring
    rw [hneg, abs_neg]
  have hplus : MDifferentiable I 𝓘(ℝ, ℝ) bplus := by
    intro x
    obtain ⟨phi, U, hU, hxU, hphi, hphiEq, hphiUpper, _hphiLap⟩ :=
      busemannFunction_exists_smooth_upper_support g hcomplete hRic gamma hline x 1 one_pos
    obtain ⟨psi, V, hV, hxV, hpsi, hpsiEq, hpsiUpper, _hpsiLap⟩ :=
      busemannFunction_exists_smooth_upper_support g hcomplete hRic
        (fun t : ℝ ↦ gamma (-t)) hreverse x 1 one_pos
    have hnegUpper : ∀ᶠ y in 𝓝 x, -bplus y ≤ psi y := by
      filter_upwards [hpsiUpper] with y hy
      rw [← hminus y]
      exact hy
    have hphiDiff : MDifferentiableAt I 𝓘(ℝ, ℝ) phi x :=
      ((hphi x hxU).contMDiffAt (hU.mem_nhds hxU)).mdifferentiableAt (by simp)
    have hpsiDiff : MDifferentiableAt I 𝓘(ℝ, ℝ) psi x :=
      ((hpsi x hxV).contMDiffAt (hV.mem_nhds hxV)).mdifferentiableAt (by simp)
    exact DifferentialGeometry.Analysis.mdifferentiableAt_of_opposite_upper_supports
      hphiDiff hpsiDiff hphiEq (hpsiEq.trans (hminus x)) hphiUpper hnegUpper
  refine ⟨hplus, ?_⟩
  intro x
  exact (hplus x).neg.congr_of_eventuallyEq (Eventually.of_forall hminus)

end SameLine

end DifferentialGeometry.Geometry.Metric

end
