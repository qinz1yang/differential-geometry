import DifferentialGeometry.Geometry.Exponential.Intrinsic.Restriction
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Agreement
import Mathlib.Basic.ENNReal.Real

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

omit [CompleteSpace E] [T2Space (TangentBundle I M)] [ConnectedSpace M] in
theorem injOn_expMap_ball_of_intrinsicInjRadius
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {r : Real}
    (hr : ENNReal.ofReal r < intrinsicInjRadius (I := I) g hEnorm p) :
    InjOn (fun v : TangentSpace I p =>
      DifferentialGeometry.Geometry.Riemannian.Exponential.expMap (I := I) g p v)
      {v : TangentSpace I p | Real.sqrt (g.inner p v v) < r} := by
  intro u hu w hw huw
  have hinj := intrinsicInjOn_ball (I := I) g hEnorm p hr
  have hmem : ∀ v : TangentSpace I p,
      Real.sqrt (g.inner p v v) < r →
        (normalFrame (I := I) g p).symm v ∈ Metric.ball (0 : E) r := by
    intro v hv
    rw [Metric.mem_ball, dist_zero_right,
      ← normalFrame_sqrt (I := I) g p ((normalFrame (I := I) g p).symm v),
      ContinuousLinearEquiv.apply_symm_apply]
    exact hv
  have hkey : intrinsicFramedExp (I := I) g hEnorm p ((normalFrame (I := I) g p).symm u) =
      intrinsicFramedExp (I := I) g hEnorm p ((normalFrame (I := I) g p).symm w) := by
    simp only [intrinsicFrame_apply, ContinuousLinearEquiv.apply_symm_apply,
      ← DifferentialGeometry.Geometry.Riemannian.Exponential.expMap_eq_expMapIntrinsic
        (I := I) g hEnorm p]
    exact huw
  exact (normalFrame (I := I) g p).symm.injective (hinj (hmem u hu) (hmem w hw) hkey)

omit [CompleteSpace E] [T2Space (TangentBundle I M)] [ConnectedSpace M] in
theorem intrinsicInjRadiusSet_restrictOpen
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (U : TopologicalSpace.Opens M) [SigmaCompactSpace U]
    [RiemannianBundle (fun x : U => TangentSpace I x)]
    [IsRiemannianManifold I U] [CompleteSpace U]
    [IsContinuousRiemannianBundle E (fun x : U => TangentSpace I x)]
    (hUEnorm : IsMetricNorm (g.restrictOpen U)) (x : U) :
    intrinsicInjRadiusSet (g.restrictOpen U) hUEnorm x =
      intrinsicInjRadiusSet g hEnorm (x : M) := by
  ext r
  change Set.InjOn (intrinsicFramedExp (g.restrictOpen U) hUEnorm x) (Metric.eball 0 r) ↔
    Set.InjOn (intrinsicFramedExp g hEnorm (x : M)) (Metric.eball 0 r)
  have heq (v : E) := intrinsicFramedExp_restrictOpen g hEnorm U hUEnorm x v
  constructor
  · intro hu v hv w hw hval
    apply hu hv hw
    apply Subtype.val_injective
    exact (heq v).trans (hval.trans (heq w).symm)
  · intro hm v hv w hw hval
    apply hm hv hw
    exact (heq v).symm.trans ((congrArg Subtype.val hval).trans (heq w))

omit [CompleteSpace E] [T2Space (TangentBundle I M)] [ConnectedSpace M] in
theorem intrinsicInjRadius_restrictOpen
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (U : TopologicalSpace.Opens M) [SigmaCompactSpace U]
    [RiemannianBundle (fun x : U => TangentSpace I x)]
    [IsRiemannianManifold I U] [CompleteSpace U]
    [IsContinuousRiemannianBundle E (fun x : U => TangentSpace I x)]
    (hUEnorm : IsMetricNorm (g.restrictOpen U)) (x : U) :
    intrinsicInjRadius (g.restrictOpen U) hUEnorm x = intrinsicInjRadius g hEnorm (x : M) := by
  unfold intrinsicInjRadius
  rw [intrinsicInjRadiusSet_restrictOpen g hEnorm U hUEnorm x]

end NormalCoordinates
end Riemannian
end Geometry
end DifferentialGeometry

end
