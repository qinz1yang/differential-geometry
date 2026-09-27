import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.CanonicalClass
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.ComparisonLimit

noncomputable section

universe u

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M] [CompactSpace M]
  [ConnectedSpace M] [SimplyConnectedSpace M]
variable {N : Type u} [TopologicalSpace N] [ChartedSpace ThreeSpace N]
  [IsManifold ThreeModel ∞ N] [T2Space N] [CompactSpace N]
  [ConnectedSpace N] [SimplyConnectedSpace N]

omit [ConnectedSpace M] [ConnectedSpace N] in
private theorem positiveHomotopyClass_eq_of_integralHomologyMap (oM : TangentOrientationSection M)
    (oN : TangentOrientationSection N) (f : C(M, N)) (p : M)
    (hf : integralHomologyMap 3 f (fundamentalClass oM) = fundamentalClass oN) :
    basedHomotopyMap f p (positiveHomotopyClass oM p) = positiveHomotopyClass oN (f p) := by
  apply (rfs_homotopy_groups (f p)).2.injective
  rw [hurewiczThree_natural, positiveHomotopyClass_hurewicz, hf,
    positiveHomotopyClass_hurewicz]

private theorem positiveFreeLoopClass_natural_of_integralHomologyMap
    (oM : TangentOrientationSection M) (oN : TangentOrientationSection N) (f : C(M, N))
    (hf : integralHomologyMap 3 f (fundamentalClass oM) = fundamentalClass oN) :
    FreeHomotopyClass.map (loopPostcompose f) (positiveFreeLoopClass oM) =
      positiveFreeLoopClass oN := by
  let q₀ : M := Classical.choice (inferInstance : Nonempty M)
  have hstep : basedHomotopyMap (loopPostcompose f) (constantLoops q₀)
      (positiveBasedLoopClass oM q₀) = positiveBasedLoopClass oN (f q₀) := by
    unfold positiveBasedLoopClass
    rw [freeLoopAdjunction_natural f (positiveHomotopyClass oM q₀),
      positiveHomotopyClass_eq_of_integralHomologyMap oM oN f q₀ hf]
  rw [positiveFreeLoopClass_eq oM q₀, positiveFreeLoopClass_eq oN (f q₀),
    forgetBasedSphere_natural f (constantLoops q₀)
      (positiveBasedLoopClass oM q₀), hstep]
  simp only [loopPostcompose_constantLoops]

theorem positiveFreeContractibleClass_natural_of_integralHomologyMap
    (oM : TangentOrientationSection M) (oN : TangentOrientationSection N) (f : C(M, N))
    (hf : integralHomologyMap 3 f (fundamentalClass oM) = fundamentalClass oN) :
    FreeHomotopyClass.map (contractibleLoopPostcompose f) (positiveFreeContractibleClass oM) =
      positiveFreeContractibleClass oN := by
  unfold positiveFreeContractibleClass
  rw [← FreeHomotopyClass.map_comp]
  have hcomp : (contractibleLoopPostcompose f).comp (toContractibleLoops (M := M)) =
      (toContractibleLoops (M := N)).comp (loopPostcompose f) := rfl
  rw [hcomp, FreeHomotopyClass.map_comp,
    positiveFreeLoopClass_natural_of_integralHomologyMap oM oN f hf]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

open Surgery.Topology

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
  [SimplyConnectedSpace M]
variable {N : Type u} [TopologicalSpace N] [ChartedSpace ThreeSpace N]
  [IsManifold ThreeModel ∞ N] [T2Space N] [CompactSpace N] [ConnectedSpace N]
  [SimplyConnectedSpace N]

theorem canonicalWidth_le_liminf_of_integralHomologyMap
    (g : ℝ → SmoothRiemannianMetric ThreeModel M) (h : SmoothRiemannianMetric ThreeModel N)
    (oM : TangentOrientationSection M) (oN : TangentOrientationSection N) (f : C(M, N))
    (hdegree : integralHomologyMap 3 f (fundamentalClass oM) = fundamentalClass oN)
    {t : ℝ} (ell : ℝ → ℝ) (hell : Tendsto ell (𝓝[<] t) (𝓝 1))
    (hlip : ∀ᶠ s in 𝓝[<] t, 0 ≤ ell s ∧ ∀ x y,
      riemannianEDistOf h (f x) (f y) ≤
        ENNReal.ofReal (ell s) * riemannianEDistOf (g s) x y) :
    ENNReal.ofReal (canonicalWidth h oN) ≤
      liminf (fun s => ENNReal.ofReal (canonicalWidth (g s) oM)) (𝓝[<] t) :=
  classWidth_le_liminf_of_lipschitzComparison g h
    (positiveFreeContractibleClass oM) (positiveFreeContractibleClass oN)
    (fun _ => f) ell hell
    (Eventually.of_forall fun _ =>
      positiveFreeContractibleClass_natural_of_integralHomologyMap oM oN f hdegree)
    hlip

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
