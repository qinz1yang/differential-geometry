import DifferentialGeometry.Geometry.Exponential.Intrinsic.Framed.Coordinates
import Mathlib.Data.ENNReal.Real

set_option autoImplicit false

noncomputable section

open Bundle Set
open scoped Topology Manifold ContDiff ENNReal NNReal Bundle

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace NormalCoordinates

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [CompleteSpace E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [PseudoEMetricSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

def intrinsicInjRadiusSet
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) : Set ℝ≥0∞ :=
  {r | InjOn (intrinsicFramedExp (I := I) g hEnorm p)
    (Metric.eball (0 : E) r)}

def intrinsicInjRadius
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) : ℝ≥0∞ :=
  sSup (intrinsicInjRadiusSet (I := I) g hEnorm p)

omit [CompleteSpace E] [T2Space (TangentBundle I M)] [ConnectedSpace M] in
lemma intrinsicInj_down
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {r r' : ℝ≥0∞} (h : r' ≤ r)
    (hr : r ∈ intrinsicInjRadiusSet (I := I) g hEnorm p) :
    r' ∈ intrinsicInjRadiusSet (I := I) g hEnorm p :=
  hr.mono (Metric.eball_subset_eball h)

omit [CompleteSpace E] [T2Space (TangentBundle I M)] [ConnectedSpace M] in
lemma zero_mem_intrInj
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) :
    (0 : ℝ≥0∞) ∈ intrinsicInjRadiusSet (I := I) g hEnorm p := by
  classical
  change InjOn _ (Metric.eball (0 : E) (0 : ℝ≥0∞))
  rw [Metric.eball_zero]
  exact Set.injOn_empty _

omit [CompleteSpace E] [T2Space (TangentBundle I M)] [ConnectedSpace M] in
lemma le_intrInjRadius
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {r : ℝ≥0∞}
    (hr : r ∈ intrinsicInjRadiusSet (I := I) g hEnorm p) :
    r ≤ intrinsicInjRadius (I := I) g hEnorm p :=
  le_sSup hr

omit [ConnectedSpace M] in
omit [CompleteSpace E] [T2Space (TangentBundle I M)] in
theorem intrinsicInjOn_eball
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {r : ℝ≥0∞}
    (hr : r < intrinsicInjRadius (I := I) g hEnorm p) :
    InjOn (intrinsicFramedExp (I := I) g hEnorm p)
      (Metric.eball (0 : E) r) := by
  classical
  rcases lt_sSup_iff.mp hr with ⟨r', hr'_mem, hr_lt_r'⟩
  exact hr'_mem.mono
    (Metric.eball_subset_eball (le_of_lt hr_lt_r'))

omit [ConnectedSpace M] in
omit [CompleteSpace E] [T2Space (TangentBundle I M)] in
theorem intrinsicInjOn_ball
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {r : Real}
    (hr : ENNReal.ofReal r < intrinsicInjRadius (I := I) g hEnorm p) :
    InjOn (intrinsicFramedExp (I := I) g hEnorm p)
      (Metric.ball (0 : E) r) := by
  have h := intrinsicInjOn_eball (I := I) g hEnorm p hr
  rwa [Metric.eball_ofReal] at h

end NormalCoordinates
end Riemannian
end Geometry
end DifferentialGeometry

end
