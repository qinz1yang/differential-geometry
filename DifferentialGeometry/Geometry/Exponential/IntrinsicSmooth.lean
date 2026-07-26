import DifferentialGeometry.Geometry.Geodesic.ChartRegularity
import DifferentialGeometry.Geometry.Exponential.IntrinsicExp

set_option linter.unusedSectionVars false

/-!
# Global `C^∞`-in-time regularity of the intrinsic geodesic

The intrinsic geodesic of a complete manifold is `C^∞` in time on all of `ℝ`
— the `C^∞` upgrade of `intrinsicGeodesic_contMDiffOn` (which gives `C¹`).
The engine is `isGeodesicOn_contMDiffOn_infty` (`Geodesic/ChartRegularity.lean`):
a moving-foot geodesic, continuous on an open time set, is `C^∞` there, with
no chart-confinement or small-radius hypothesis.

This removes the time-regularity half of the `expMapC2Radius`-type caps: the
radial geodesic `t ↦ exp_p(t·x)` in its intrinsic form is smooth on every
compact window, for every launch vector.
-/

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

open DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [Module.Finite ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **The intrinsic geodesic is `C^∞` in time on all of `ℝ`.**  `C^∞` upgrade
of `intrinsicGeodesic_contMDiffOn`. -/
theorem intrinsicGeodesic_contMDiffOn_infty
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) :
    ContMDiffOn 𝓘(ℝ, ℝ) I ∞ (intrinsicGeodesic (I := I) g hEnorm p v)
      Set.univ := by
  refine isGeodesicOn_contMDiffOn_infty (I := I) g isOpen_univ ?_ ?_
  · exact (intrinsicGeodesic_isGeodesic (I := I) g hEnorm p v).isGeodesicOn
      Set.univ
  · exact (intrinsicGeodesic_continuous (I := I) g hEnorm p v).continuousOn

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **The intrinsic geodesic is globally `C^∞` in time** (unrestricted
`ContMDiff` form of `intrinsicGeodesic_contMDiffOn_infty`, for consumers that
ask for `ContMDiff` on all of `ℝ`, e.g. the parallel-frame producer). -/
theorem intrinsicGeodesic_contMDiff
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (v : TangentSpace I p) :
    ContMDiff 𝓘(ℝ, ℝ) I ∞ (intrinsicGeodesic (I := I) g hEnorm p v) :=
  contMDiffOn_univ.mp
    (intrinsicGeodesic_contMDiffOn_infty (I := I) g hEnorm p v)

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry
