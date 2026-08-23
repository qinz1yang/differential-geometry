import DifferentialGeometry.Geometry.Exponential.IntrinsicFramedCoordinates
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

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable [PseudoEMetricSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

def intrInjRadiusSet
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) : Set ℝ≥0∞ :=
  {r | InjOn (intrinsicFramedExp (I := I) g hEnorm p)
    (Metric.eball (0 : E) r)}

def intrInjRadius
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) : ℝ≥0∞ :=
  sSup (intrInjRadiusSet (I := I) g hEnorm p)

omit [CompleteSpace E] [T2Space (TangentBundle I M)] [ConnectedSpace M] in
lemma intrInj_down
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {r r' : ℝ≥0∞} (h : r' ≤ r)
    (hr : r ∈ intrInjRadiusSet (I := I) g hEnorm p) :
    r' ∈ intrInjRadiusSet (I := I) g hEnorm p :=
  hr.mono (Metric.eball_subset_eball h)

omit [CompleteSpace E] [T2Space (TangentBundle I M)] [ConnectedSpace M] in
lemma zero_mem_intrInj
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) :
    (0 : ℝ≥0∞) ∈ intrInjRadiusSet (I := I) g hEnorm p := by
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
    (hr : r ∈ intrInjRadiusSet (I := I) g hEnorm p) :
    r ≤ intrInjRadius (I := I) g hEnorm p :=
  le_sSup hr

omit [ConnectedSpace M] in
omit [CompleteSpace E] [T2Space (TangentBundle I M)] in
theorem intrInjOn_eball
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {r : ℝ≥0∞}
    (hr : r < intrInjRadius (I := I) g hEnorm p) :
    InjOn (intrinsicFramedExp (I := I) g hEnorm p)
      (Metric.eball (0 : E) r) := by
  classical
  rcases lt_sSup_iff.mp hr with ⟨r', hr'_mem, hr_lt_r'⟩
  exact hr'_mem.mono
    (Metric.eball_subset_eball (le_of_lt hr_lt_r'))

omit [ConnectedSpace M] in
omit [CompleteSpace E] [T2Space (TangentBundle I M)] in
theorem intrInjOn_ball
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {r : Real}
    (hr : ENNReal.ofReal r < intrInjRadius (I := I) g hEnorm p) :
    InjOn (intrinsicFramedExp (I := I) g hEnorm p)
      (Metric.ball (0 : E) r) := by
  have h := intrInjOn_eball (I := I) g hEnorm p hr
  rwa [Metric.eball_ofReal] at h

end NormalCoordinates
end Riemannian
end Geometry
end DifferentialGeometry

end
