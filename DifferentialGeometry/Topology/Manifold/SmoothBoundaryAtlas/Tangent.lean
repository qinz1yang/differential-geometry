import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

noncomputable section

open Set Filter Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.SmoothBoundaryAtlas

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ} [NeZero n] {K : Set M} (C : SmoothBoundaryAtlas I n K)

theorem mfderiv_subtypeVal_bijective (x : K) :
    let _ := C.toChartedSpace
    let _ := C.isManifold
    Function.Bijective (mfderiv (𝓡∂ n) I (Subtype.val : K → M) x) := by
  let _ := C.toChartedSpace
  let _ := C.isManifold
  let a := C.ambientChart x
  have ha : MDifferentiableAt I (𝓡 n) a x.val :=
    (a.contMDiffOn.contMDiffAt (a.open_source.mem_nhds (C.mem_source x))).mdifferentiableAt
      (by simp)
  have hi : MDifferentiableAt (𝓡∂ n) I (Subtype.val : K → M) x :=
    C.contMDiff_subtype_val.mdifferentiableAt (by simp)
  have heq : (a ∘ (Subtype.val : K → M)) =ᶠ[𝓝 x] extChartAt (𝓡∂ n) x := by
    filter_upwards [(C.chart x).open_source.mem_nhds (C.mem_source x)] with y hy
    change a y.val = (C.chart x y).val
    exact (OpenPartialHomeomorph.restrictSubtypes_apply _ _ _ _ _ _ _ hy).symm
  have hcomp : (mfderiv I (𝓡 n) a x.val).comp
      (mfderiv (𝓡∂ n) I (Subtype.val : K → M) x) =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
    rw [← mfderiv_comp x ha hi, heq.mfderiv_eq, mfderiv_extChartAt_self]
    rfl
  have hloc := a.isLocalDiffeomorphAt I (𝓡 n) ∞ (C.mem_source x)
  have hbij : Function.Bijective (mfderiv I (𝓡 n) a x.val) := by
    rw [← hloc.mfderivToContinuousLinearEquiv_coe (by simp)]
    exact (hloc.mfderivToContinuousLinearEquiv (by simp)).bijective
  constructor
  · intro v w hvw
    have hv := congrArg (fun L => L v) hcomp
    have hw := congrArg (fun L => L w) hcomp
    change mfderiv I (𝓡 n) a x.val
      (mfderiv (𝓡∂ n) I (Subtype.val : K → M) x v) = v at hv
    change mfderiv I (𝓡 n) a x.val
      (mfderiv (𝓡∂ n) I (Subtype.val : K → M) x w) = w at hw
    rw [hvw] at hv
    exact hv.symm.trans hw
  · intro v
    refine ⟨mfderiv I (𝓡 n) a x.val v, hbij.injective ?_⟩
    exact congrArg (fun L => L (mfderiv I (𝓡 n) a x.val v)) hcomp

end DifferentialGeometry.Topology.SmoothBoundaryAtlas
